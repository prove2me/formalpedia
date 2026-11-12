-- Prove2me | Theorems.Thm_FourMsgQMA_corollary_5_15
-- name    : FourMsgQMA.corollary_5_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:39:17.148648+00:00
-- url     : https://prove2.me/theorems/0626c9de-2b39-486c-ada4-0465c5244266
-- title:
--   Corollary 5.15 — succinct four-message arguments for NP ∘ batchQMA from LWE
-- statement:
--   This is Corollary 5.15 (four-message circuit batch arguments from LWE) in the pinned-down version requested by the operator.
--
--   Fix $\varepsilon\in(0,1)$ and assume $\mathrm{Hyp}(\varepsilon)$: LWE with polynomial dimension, modulus at most $2^{n^\varepsilon}$ and discrete Gaussian error of width at least $2\sqrt n$. Let $L$ be a QMA promise problem with uniform verification family $F$. Then there is one four-message argument $\Pi$ with a classical verifier. It takes the policy and the batch $u=(C,X)$ as input, and has all of the following properties:
--
--   1. **uniform**: its preprocessing, verifier stages, decision and honest prover are polynomial time;
--   2. **overwhelmingly complete**: for every polynomial size bound there is a negligible $\nu$ such that, for every admissible $(C,X)$, every authorized $y$ selecting only yes-instances and every choice of $\rho_i\in W_Q(x_i,2/3)$, the honest prover with $(y,a)$ and $\bigotimes_{i:y_i=1}\rho_i^{\otimes N}$ is accepted with probability at least $1-\nu(\lambda)$;
--   3. **negligibly selectively sound** (Definition 3.6): for every fixed sequence of polynomial-size no-instances $X_\lambda\in L^{C_\lambda}_{\mathrm{no}}$ and every nonuniform QPT prover with quantum advice, the acceptance probability is negligible;
--   4. **succinct**: for one polynomial $p$, every message and the online verifier work ($V_2$ and $\mathrm{Dec}$) are bounded by
--   $$
--   p\big(\lambda,\ t(X),\ \lceil\log_2(k+1)\rceil,\ \lceil\log_2(s+1)\rceil\big),
--   $$
--   and answers longer than that are rejected;
--   5. **prover-efficient**: the honest prover has size polynomial in $(\lambda,t(X),k,s)$ and uses $N(\lambda,t)$ copies of each selected witness, $N$ polynomial.
--
--   Here $t(X)=\max_it_L(x_i)$ replaces the paper's local resource bound $T$. This is the paper's headline result. It answers the first question of the introduction: NP ∘ batchQMA, including non-monotone policies, has four-message classical-verifier arguments with negligible errors whose communication is polylogarithmic in the batch and policy sizes.
--
--   Differences from the source:
--   - reading: "Assume post-quantum LWE as in Assumption 3.10, at the parameters supporting the base protocol and the primitive instantiations in Section 3"; "The LWE parameter family is that required by these instantiations" → Hyp(ε) for the given ε ∈ (0,1): LWE (Assumption 3.10's game) for every efficiently computable (n, q, σ) with polynomial n ≥ max(λ,1), 2 ≤ q ≤ 2^{n^ε}, discrete Gaussian error D_{ℤ,σ} with σ ≥ 2√n; reason: the paper fixes no family ("Each instantiation specifies its family", p.15); it keeps a superpolynomial modulus-to-noise ratio (p.14) and GSW needs q > 8(M+1)^L B with dimension and log q polynomial (p.18), i.e. ratio 2^{poly}; σ ≥ 2√n is Regev's regime
--   - encoding: QPT adversaries and distinguishers: nonuniform polynomial-size quantum circuit families with one quantum advice state (§3.1, p.9) → the published TightPQRepetition.Main.IsQPT strategies and IsQTestFamily distinguishers (gate set: all one- and two-qubit unitaries), on both sides of the implication; reason: a finite universal gate set approximates these circuits to negligible error at polynomial cost (Solovay–Kitaev), so the classes give the same negligible-advantage statements
--   - reading: PPT verifier stages (Pre, V1, V2), deterministic Dec, QPT honest prover (§3.3); "Policy and batch preprocessing, including primitive setup, are charged as in the construction above" → Arg4.IsUniform: every algorithm PolyTimeComputable on its packed inputs with explicit uniform coins; the honest prover is a quantum core over H, S, T, X, CNOT generated in polynomial time from (1^λ, u, y, a), with polynomial-time controllers; reason: the construction's preprocessing cost (p.38) is polynomial time; the paper fixes no machine model
--   - reading: the honest resource set W_Π(u): "the prescribed polynomial number of independent copies of valid QMA witnesses" (p.10), "an authorized vector y, its policy wire values, and the required QMA witness copies at each selected coordinate" (p.36) → every authorized y selecting only yes-instances, its wire values a, and ⊗_{i: y_i=1} ρ_i^{⊗N(λ,t(X))} for arbitrary density operators ρ_i ∈ W_Q(x_i, 2/3); N chosen by the scheme, polynomial; reason: threshold 2/3 is the QMA convention of p.10; fixing the resource in the statement prevents an empty resource set
--   - encoding: the local resource bound T → t(X) = max_i (|x_i| + witness wires + ancilla wires + 1 + depth of Q_{x_i}); reason: T is polynomial in λ and the cost of verifying one QMA instance and t ≤ T (p.9), so a polynomial bound in (λ, T) and one in (λ, t) are the same claim
--   - encoding: log(k+1), log(s+1) → ⌈log₂(k+1)⌉, ⌈log₂(s+1)⌉ (Nat.clog 2); reason: standard integer rounding; inside a polynomial bound it changes nothing
--   - reading: "Its communication and online verifier work are poly(λ, T, log(k + 1), log(s + 1))"; "After preprocessing and generation of q1, the total verifier work is bounded by the same polynomial" (p.12) → Arg4.Succinct: one polynomial p; |q1|, |q2| ≤ p; every honest answer has length ≤ p and Dec accepts only answers of length ≤ p; V2 and Dec computed by circuits of size ≤ p on the inputs that occur for instances with the same (t, k, s); reason: "These are worst-case size and time bounds, including rejected malformed messages of allowed length" (p.12); the polynomial is "fixed by the scheme, independently of the actual inputs and setup outcomes" (p.9)
--   - reading: "every polynomial-size Boolean circuit policy admits a four-message … argument" → for each L and F, one scheme Arg4 that takes u = (C, X) as input and works for every k ≥ 1, s ≥ 0 and every canonical C; reason: the construction of §5.1 is uniform in C; this is the stronger reading
--   - reading: the quantifier convention of §3.1: ∀ polynomial resource bounds ∀ A ∀ {ζλ} ∃ ν ∈ negl ∀ λ → completeness: ∀ size bound B ∃ ν negligible ∀ λ ∀ u with |u| ≤ B(λ); soundness: ∀ B ∀ sequence u_λ ∈ noSet with |u_λ| ≤ B(λ) ∀ IsQPT adversary, acceptance negligible; reason: p.9; Definition 3.6 fixes C and X before preprocessing
--   - encoding: [k] = {1, …, k}, canonical circuit tables and instance encodings → Fin k with i ↦ i+1; PolicyCircuit with the 1-based indices of Figure 4; Inst.encode = pack (circuit table :: batch); reason: Lean representation
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Corollary 5.15, p.44 (PDF 46); Definition 3.6, p.13; §3.3, pp.11–12; §5.1, pp.34–38

import Mathlib
import Definitions.Def_FourMsgQMA_LWEHyp
import Definitions.Def_FourMsgQMA_Arg4_IsUniform
import Definitions.Def_FourMsgQMA_Arg4_Complete
import Definitions.Def_FourMsgQMA_Arg4_SelectivelySound
import Definitions.Def_FourMsgQMA_Arg4_Succinct
import Definitions.Def_FourMsgQMA_Arg4_ProverEfficient

namespace FourMsgQMA

open QAlgorithms.Complexity

/-- **Corollary 5.15** (Four-message circuit batch arguments from LWE), Goyal, Koppula, STOC 2027
submission (sha256 6c523d45…), p.44 (PDF 46), pinned-down version (operator request).

For every `ε ∈ (0, 1)`, if post-quantum LWE holds in the regime `Hyp(ε)` (polynomial dimension,
modulus at most `2^{n^ε}`, discrete Gaussian error of width at least `2√n`), then for every QMA
promise problem `L` with uniform verification-circuit family `F` there is one four-message
classical-verifier argument for NP ∘ batchQMA(`L`), taking the policy and the batch `u = (C, X)` as
input, that is uniform and polynomial-time (`IsUniform`), overwhelmingly complete for every honest
resource (`Complete`), negligibly selectively sound against nonuniform QPT provers with quantum
advice (`SelectivelySound`, Definition 3.6), has every message and its online verifier work bounded
by `p(λ, t(X), ⌈log₂(k+1)⌉, ⌈log₂(s+1)⌉)` for one polynomial `p` (`Succinct`), and has an honest
prover of size polynomial in `(λ, t(X), k, s)` using polynomially many witness copies
(`ProverEfficient`).

**Formalization Note** Pinned-down version (operator request): LWE regime `Hyp(ε)`; adversaries
`TightPQRepetition.Main.IsQPT`; uniform polynomial-time verifier stages and honest prover; honest
resource `⊗_{i : y_i = 1} ρ_i^{⊗N}` with `ρ_i ∈ W_Q(x_i, 2/3)`; `t(X)` in place of `T`;
`⌈log₂⌉`; one scheme for all `(C, X)`. -/
theorem corollary_5_15 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hLWE : LWEHyp ε)
    (L : PromiseProblem) (F : QMAFamily) (hLF : IsQMAVerifierFor L F) :
    ∃ A : Arg4, A.IsUniform ∧ A.Complete L F ∧ A.SelectivelySound L ∧ A.Succinct F ∧
      A.ProverEfficient F := by sorry

end FourMsgQMA
