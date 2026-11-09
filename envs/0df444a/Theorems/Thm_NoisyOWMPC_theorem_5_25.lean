-- Prove2me | Theorems.Thm_NoisyOWMPC_theorem_5_25
-- name    : NoisyOWMPC.theorem_5_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:03:19.691857+00:00
-- url     : https://prove2.me/theorems/b9ec86ae-bdab-4d58-b4b6-148d67207cc7
-- title:
--   Theorem 5.25 — correctness and coalition security
-- statement:
--   Let $\mathbf C$ be a product broadcast channel with every $C_i$ nonconstant. Fix recoverable access tests (Definition 5.2; for $k=1$ the trivial test with $\alpha=\delta_{\mathrm{acc}}=0$) with errors $(\alpha,\delta_{\mathrm{acc}})$, recoverable release tests (Definition 5.3) with errors $(\eta,\delta_{\mathrm{rel}})$, a recoverable selector on $[N]$ (Definition 5.4) with errors $(\alpha_{\mathrm{sel}},\delta_{\mathrm{sel}})$, and polynomial target circuits $f_i$, with public polynomial lengths $n_{\mathrm{acc}},n_{\mathrm{rel}},N$. Let $i\mathcal O$ be an indistinguishability obfuscator and $F$ an injective one-way function whose input length is at most every seed length. Then for every polynomial-time Fig. 6 generator there is a polynomial $s_0$ such that for every public polynomial pad size $s\ge s_0$, Construction 5.23
--   1. has correctness error at most $k\alpha+q(N\eta+\alpha_{\mathrm{sel}})+\mathrm{negl}(\lambda)$;
--   2. for every receiver-only coalition $J\subseteq[k]$ has security error (in the sense of $\approx^c$)
--   $$\epsilon_J\le(k-|J|)(\alpha+\delta_{\mathrm{acc}})+Nq_J\delta_{\mathrm{rel}}+q_J\delta_{\mathrm{sel}}+qN\eta+q_{-J}\alpha_{\mathrm{sel}}+\mathrm{negl}(\lambda);\qquad(5.13)$$
--   3. for every coalition $\{S\}\cup J$ has security error at most $(k-|J|)\alpha+q_{-J}(N\eta+\alpha_{\mathrm{sel}})+\mathrm{negl}(\lambda)$, with $q_{-J}=q-q_J$;
--   4. is Las Vegas, uses $\mathbf 1[k>1]\,kn_{\mathrm{acc}}+qNn_{\mathrm{rel}}$ noisy channel uses and $|\tilde P|$ broadcast bits.
--   5. is a protocol in the sense of Definition 4.2: its lengths are polynomial, its receivers are deterministic polynomial-time algorithms, and its sender is implemented in polynomial time within statistical distance $(k+q+qN)2^{-\lambda}$.
--
--   Differences from the source:
--   - generalization: 'assuming iO and one-way functions', with the paper's fixed injective OWF F → every iO scheme and every injective one-way function F with input length at most every seed length; reason: Theorem 3.4 gives such an F from iO and one-way functions; the paper's F is one of them
--   - generalization: the paper's program padded to 'a common public polynomial size' → every polynomial-time Fig. 6 generator and every polynomial pad size above some s₀; reason: the paper's implementation is one such generator and size
--   - encoding: negl(λ) in the coalition bounds → the distinguisher-dependent negligible term of ≈^c in the security definition; reason: Definition 4.2's security notion
--   - encoding: |P̃| broadcast bits → τ is the length-prefixed obfuscation padded to a fixed public length txLen; reason: §5 Conventions, p.21
--   - generalization: recoverable release tests with p′ ∈ (0,1) in unbiasedness (Definition 5.3) → p′ ∈ [0,1] with |p′ − ½| ≤ η; reason: a weaker hypothesis; every test with p′ ∈ (0,1) qualifies, and the error bounds do not use the strict inequality
--   - encoding: samplers implemented within statistical error 2^{−λ} → exact reference distributions; efficiency clauses ask for a polynomial-time sampler within 2^{−λ}; reason: the paper's own convention: 'The distributions above are exact reference distributions' (p.24)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
--   - encoding: Definition 3.2: iO returns a circuit with 'polynomially bounded description'; obfuscations 'padded to a fixed public length' (p.21) → IOScheme carries a public length bound len(λ, n, s), polynomial and computable in polynomial time, on every obfuscated description; reason: every obfuscator with polynomially bounded descriptions has such a bound; it fixes the public transmission length
--   - encoding: for k = 1 'the trivial test that always accepts' (Definition 5.2) → channel-input length 0, one state with weight 1 encoded by the empty string, every query accepted (TestHalf.IsTrivial); reason: the trivial test has one state; its encoding carries no information
--   - reading: 'Construction 5.23 realizes these targets in Definition 4.2' (a protocol with PPT sender, deterministic receivers and polynomial lengths) → adds polynomial L and N, deterministic polynomial-time receivers, and a polynomial-time sender within statistical distance (k + q + qN)·2^{−λ} of the exact reference sender; reason: each of the k + qN + q sampled states comes from a sampler within 2^{−λ} (§5 Conventions, p.21: 'All samplers are implemented in polynomial time to within statistical error 2^{−λ}'); the paper absorbs these errors
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem 5.25, p.31

import Mathlib
import Definitions.Def_NoisyOWMPC_construction
import Definitions.Def_NoisyOWMPC_SecErr
import Definitions.Def_NoisyOWMPC_ChannelTest
import Definitions.Def_NoisyOWMPC_Selector
import Definitions.Def_NoisyOWMPC_KeyedFamily
import Definitions.Def_NoisyOWMPC_CoinAlg

namespace NoisyOWMPC

/-- **Theorem 5.25 (Correctness and coalition security)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Theorem 5.25, p.31): "Let `C` be a fixed product broadcast channel
with every `C_i` nonconstant. Fix recoverable access and release tests, a recoverable selector on
`[N]`, and public target circuits `f_i(x; ρ_i)` as in Construction 5.23, with all seed lengths at
least the input length of `F`. Assuming iO and one-way functions, Construction 5.23 realizes these
targets in Definition 4.2 with the following errors, and is Las Vegas (Definition 4.3).
• Correctness: at most `kα + q(Nη + α_sel) + negl(λ)`.
• Receiver-only coalitions `J ⊆ [k]`:
`ε_J ≤ (k − |J|)(α + δ_acc) + Nq_Jδ_rel + q_Jδ_sel + qNη + q_{−J}α_sel + negl(λ)`. (5.13)
• Coalitions containing the sender `{S} ∪ J`: at most `(k − |J|)α + q_{−J}(Nη + α_sel) + negl(λ)`,
where `q_{−J} = q − q_J`. The protocol uses `1[k > 1] kn_acc + qNn_rel` noisy channel uses and `|P̃|`
broadcast bits."

The access tests are recoverable with errors `(α, δ_acc)` when `k > 1` and trivial with
`α = δ_acc = 0` when `k = 1` (Definition 5.2); the release tests are recoverable with errors
`(η, δ_rel)`; the selector is recoverable with errors `(α_sel, δ_sel)`; `F` is an injective one-way
function (§5 Conventions, p.21) whose input length all seed lengths exceed.

**Formalization Note** "Assuming iO and one-way functions" is an iO scheme `O` and an injective
one-way function `Finj`, which they give by Theorem 3.4. The program is padded to `s` gates for
every public polynomial `s` above some `s₀` (§5 Conventions, p.21); the lengths `n_acc`, `n_rel`,
`N` are public polynomial parameters (Definition 4.2, p.18). The `negl(λ)` terms of the coalition
bounds are those of `≈^c` in `Protocol.SecErr`; the broadcast length is the transmission length
`txLen` of the obfuscated program. "Realizes … in Definition 4.2" includes the protocol's syntax:
polynomial lengths, deterministic polynomial-time receivers, and a polynomial-time sender, which is
within statistical distance `(k + q + qN)2^{−λ}` of the exact reference sender since each of its
`k + qN + q` sampled states comes from a sampler within `2^{−λ}` (§5 Conventions, p.21). -/
theorem theorem_5_25 {k : ℕ} (hk : 1 ≤ k) {X : Type} [Fintype X] {Y : Fin k → Type}
    [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i)) (hC : ∀ i, Nonconstant (C i))
    (nacc nrel N : ℕ → ℕ) (A : ∀ i, ChannelTest k X Y i nacc (Finset.univ.erase i))
    (R : ∀ i, ChannelTest k X Y i nrel Finset.univ)
    (hpar : PolyParam nacc ∧ PolyParam nrel ∧ PolyParam N)
    (S : Selector N) (α δacc η δrel αsel δsel : ℕ → ℝ)
    (hA : (1 < k → ∀ i, (A i).IsRecAccess C α δacc) ∧
      (¬ 1 < k → (∀ i, (A i).toTestHalf.IsTrivial) ∧ ∀ lam, α lam = 0 ∧ δacc lam = 0))
    (hR : ∀ i, (R i).IsRecRelease C η δrel) (hS : S.IsRecSelector αsel δsel)
    (F : Functionality k) (hF : F.IsPolyCircuit)
    (O : IOScheme) (hO : O.IsIO) (Finj : KeyedFamily) (hFinj : Finj.IsInjOWF)
    (hseed : (1 < k → ∀ i lam, Finj.n lam ≤ (A i).κ lam) ∧ (∀ i lam, Finj.n lam ≤ (R i).κ lam) ∧
      ∀ lam, Finj.n lam ≤ S.κ lam) :
    let H : Halves k X Y := ⟨nacc, nrel, N, fun i => (A i).toTestHalf, fun i => (R i).toTestHalf,
      S.toSelHalf⟩
    ∀ gen : ProgGen H F, IsFig6Gen H F gen →
      ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyParam s → (∀ lam, s₀ lam ≤ s lam) →
        (∃ ν₀ : ℕ → ℝ, Negligible ν₀ ∧
          (construction H F O gen s).CorrErr C (fun lam => (k : ℝ) * α lam +
            (F.qOf Finset.univ lam : ℝ) * ((N lam : ℝ) * η lam + αsel lam) + ν₀ lam)) ∧
        (∀ J : Finset (Fin k), (construction H F O gen s).SecErr C false J (fun lam =>
          ((k : ℝ) - J.card) * (α lam + δacc lam) + (N lam : ℝ) * (F.qOf J lam : ℝ) * δrel lam +
            (F.qOf J lam : ℝ) * δsel lam + (F.qOf Finset.univ lam : ℝ) * (N lam : ℝ) * η lam +
            ((F.qOf Finset.univ lam : ℝ) - F.qOf J lam) * αsel lam)) ∧
        (∀ J : Finset (Fin k), (construction H F O gen s).SecErr C true J (fun lam =>
          ((k : ℝ) - J.card) * α lam +
            ((F.qOf Finset.univ lam : ℝ) - F.qOf J lam) * ((N lam : ℝ) * η lam + αsel lam))) ∧
        (construction H F O gen s).LasVegas C ∧
        (∀ lam, (construction H F O gen s).N lam =
          (if 1 < k then k * nacc lam else 0) + F.qOf Finset.univ lam * N lam * nrel lam) ∧
        (∀ lam, (construction H F O gen s).L lam = txLen H F O gen s lam) ∧
        PolyBounded (construction H F O gen s).L ∧ PolyBounded (construction H F O gen s).N ∧
        (∃ Ssam : CoinAlg, Ssam.IsPPT ∧ ∀ (lam : ℕ) (x : Fin (F.lx lam) → Bool),
          sdPush (unifW (Fin (Ssam.coins lam) → Bool))
              (fun ρ => Ssam.run lam (LaconicBarrier.bits x) ρ)
              ((construction H F O gen s).wS lam)
              (fun r => QAdvFew.PoQOracle.tup [(construction H F O gen s).encRS lam r,
                LaconicBarrier.bits ((construction H F O gen s).send lam x r).1,
                wordEnc X ((construction H F O gen s).send lam x r).2]) ≤
            ((k : ℝ) + (F.qOf Finset.univ lam : ℝ) + (F.qOf Finset.univ lam : ℝ) * (N lam : ℝ)) *
              (2 : ℝ) ^ (-(lam : ℤ))) ∧
        ∀ i, LaconicBarrier.PolyTimeOn
          (ι := (lam : ℕ) × (Fin ((construction H F O gen s).L lam) → Bool) ×
            (Fin ((construction H F O gen s).N lam) → Y i))
          (fun z => [LaconicBarrier.unary z.1, LaconicBarrier.bits z.2.1, wordEnc (Y i) z.2.2])
          (fun z => optEnc ((construction H F O gen s).recv z.1 i z.2.1 z.2.2)) := by sorry

end NoisyOWMPC
