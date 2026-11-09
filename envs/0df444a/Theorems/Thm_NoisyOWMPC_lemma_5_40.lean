-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_40
-- name    : NoisyOWMPC.lemma_5_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:03:16.003415+00:00
-- url     : https://prove2.me/theorems/47ce3716-6550-4b9e-822f-268623795c04
-- title:
--   Lemma 5.40 — statistical simulation for coalitions containing the sender
-- statement:
--   In the setting of Theorem 5.25, consider Construction 5.23 with an iO scheme, a Fig. 6 program generator and a pad size that every program fits. For $T=\{S\}\cup J$ let $\mathrm{Sim}_T(1^\lambda,x,\bar{\mathbf y}_J)$ run the sender on $x$, retain its coins, $\tau$ and its word, sample the corrupted receivers' observations, and return their joint view together with the sender view. There is a negligible $\nu$ such that for every $\lambda$, $x$ and $J$,
--   $$\mathrm{SD}\Bigl((x,\mathbf y_{-J},\mathrm{view}_T),\ (x,\bar{\mathbf y}_{-J},\mathrm{Sim}_T(1^\lambda,x,\bar{\mathbf y}_J))\Bigr)\le(k-|J|)\alpha+q_{-J}(N\eta+\alpha_{\mathrm{sel}})+\nu(\lambda).$$
--
--   Differences from the source:
--   - generalization: recoverable tests and selector (Theorem 5.25's setting) → only completeness, unbiasedness, honest acceptance and balance, with probability laws; reason: recoverable tests and selectors have these properties
--   - generalization: the paper's padded program → every polynomial-time Fig. 6 generator and every pad size the program fits; reason: the paper's implementation is one such generator
--   - encoding: sampling the corrupted receivers' observations → the simulator draws the joint channel output of all receivers and keeps those in J; reason: same law as drawing only J's coordinates (product channel)
--   - reading: negl(λ) → one negligible ν, uniform over x and J; reason: the paper's negligible terms are sampler-precision terms independent of x
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
--   - encoding: for k = 1 'the trivial test that always accepts' (Definition 5.2) → channel-input length 0, one state with weight 1 encoded by the empty string, every query accepted (TestHalf.IsTrivial); reason: the trivial test has one state; its encoding carries no information
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.40, p.38

import Mathlib
import Definitions.Def_NoisyOWMPC_construction
import Definitions.Def_NoisyOWMPC_SecErr

namespace NoisyOWMPC

/-- **Lemma 5.40 (Statistical simulation for coalitions containing the sender)** (Ishai, Lu, Zafar,
STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.40, p.38, in the setting of Theorem
5.25, p.31): "For `T = {S} ∪ J`, define `Sim_T(1^λ, x, ȳ_J)` by running the sender on `x`,
retaining its random coins, `τ`, and its word, sampling the corrupted receivers' observations, and
returning their joint view together with the sender view. For every `x`,
`SD((x, y_{−J}, view_T), (x, ȳ_{−J}, Sim_T(1^λ, x, ȳ_J))) ≤ (k − |J|)α + q_{−J}(Nη + α_sel) +
negl(λ)`."

The ideal side samples the ideal coins `ρ` and, independently, the simulator's sender run and
channel outputs; `q_{−J} = q − q_J`.

**Formalization Note** The simulator draws the joint channel output of all receivers and keeps the
coordinates in `J` (the same law as drawing only `J`'s). Only the properties the lemma uses are
assumed of the tests and the selector, as in `lemma_5_26`. -/
theorem lemma_5_40 {k : ℕ} (hk : 1 ≤ k) {X : Type} [Fintype X] {Y : Fin k → Type}
    [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i)) (hC : ∀ i, Nonconstant (C i))
    (H : Halves k X Y) (F : Functionality k) (hF : F.IsPolyCircuit) (α η αsel : ℕ → ℝ)
    (hacc : (1 < k → ∀ i, (H.acc i).IsDist ∧ (H.acc i).Complete C α) ∧
      (¬ 1 < k → (∀ i, (H.acc i).IsTrivial) ∧ ∀ lam, α lam = 0))
    (hrel : ∀ i, (H.rel i).IsDist ∧ (H.rel i).Unbiased C η)
    (hsel : H.sel.IsDist ∧ H.sel.HonestAccept αsel ∧ H.sel.Balanced)
    (O : IOScheme) (hO : O.IsIO) (gen : ProgGen H F) (hgen : IsFig6Gen H F gen) (s : ℕ → ℕ)
    (hs : ∀ lam x c, (gen lam x c).base.gates.length ≤ s lam) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ lam (x : Fin (F.lx lam) → Bool) (J : Finset (Fin k)),
        sdPush ((construction H F O gen s).realW C lam x)
            ((construction H F O gen s).realTuple true J lam x)
            (fun z : (∀ i, Fin (F.r i lam) → Bool) × ((construction H F O gen s).RS lam ×
                (Fin ((construction H F O gen s).N lam) → ∀ i, Y i)) =>
              unifW (∀ i, Fin (F.r i lam) → Bool) z.1 * (construction H F O gen s).realW C lam x z.2)
            (fun z => QAdvFew.PoQOracle.tup [LaconicBarrier.bits x,
              outsEnc (fun i => i ∉ J) (fun i => some (F.f lam i x (z.1 i))),
              (construction H F O gen s).viewEnc true J lam x z.2]) ≤
          ((k : ℝ) - J.card) * α lam +
            ((F.qOf Finset.univ lam : ℝ) - F.qOf J lam) * ((H.N lam : ℝ) * η lam + αsel lam) +
            ν lam := by sorry

end NoisyOWMPC
