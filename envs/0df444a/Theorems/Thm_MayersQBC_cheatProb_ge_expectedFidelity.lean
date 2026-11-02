-- Prove2me | Theorems.Thm_MayersQBC_cheatProb_ge_expectedFidelity
-- name    : MayersQBC.cheatProb_ge_expectedFidelity
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:27:10.715391+00:00
-- url     : https://prove2.me/theorems/385b48a2-c281-4472-be15-087e07d8fa8b
-- title:
--   Section e, p.4 — averaged over transcripts, Alice's cheating probability lies between $\mathbb E_\gamma F'(\gamma)$ and 1
-- statement:
--   Fix one value of the security parameter. Let $\Gamma$ be the finite set of transcripts, $p$ their law when Alice commits to $0$ (nonnegative, summing to $1$) and $q$ their law when she commits to $1$. For each $\gamma$ let $\psi'_{0,\gamma}, \psi'_{1,\gamma}$ be unit vectors of $A \otimes B$ (the states after commit′; $A$ is Alice's side, $B$ Bob's) and let $\Pi_\gamma$ be an effect ("the honest unveil of $1$ returns $1$") with $\langle \psi'_{1,\gamma}|\Pi_\gamma|\psi'_{1,\gamma}\rangle = 1$ whenever $q(\gamma) \ne 0$ (correctness). Then there are unitaries $U_\gamma$ on Alice's side such that
--
--   $$
--   \mathbb E_\gamma F'(\gamma) \;\le\; \sum_{\gamma} p(\gamma)\,\big\langle\psi'_{0,\gamma}\big|(U_\gamma\otimes I)^\dagger\,\Pi_\gamma\,(U_\gamma\otimes I)\big|\psi'_{0,\gamma}\big\rangle \;\le\; 1 ,
--   $$
--
--   where $\mathbb E_\gamma F'(\gamma)$ is the expected fidelity of Bob's reduced states (with $F'(\gamma) = 0$ when $q(\gamma) = 0$) and the middle term is Alice's probability of unveiling $1$ after an honest commitment to $0$ (definitions `expectedFidelity` and `cheatProb`).
--
--   This is the quantitative content of the paper's sentence "Alice can change the bit $b$ that she unveils to Bob from $0$ to $1$ with a probability that goes to $1$ as the expected value of $F'(\gamma)$ goes to $1$" at a single parameter value; the upper bound $1$ makes the lower bound a squeeze.
--
--   **Formalization Note** Alice's side is the first tensor factor, so her unitaries act as `Matrix.kronecker (U γ) 1`; $F'$ is Jozsa's fidelity, `rootFidelity ^ 2`.
--
--   Differences from the source:
--   - generalization: the cheating probability goes to 1 as the expected value of F′(γ) goes to 1 → at each parameter value, E_γ F′(γ) ≤ cheating probability ≤ 1; reason: the explicit two-sided bound implies the limit statement by squeezing
--   - generalization: one quantum bit commitment protocol in the model of section b → arbitrary finite types Γ, A, B, any transcript laws p, q, any unit vectors ψ0 γ, ψ1 γ and any effects acc γ; reason: every protocol of the model yields such data (finite register spaces, a finite transcript set, the honest unveil of 1 composed with Bob's verdict is an effect for each transcript), so the protocol is a special case
--   - generalization: q is the law of the transcript under commit(1) → q is any real function; only its zero set is used; reason: the transcript law under commit(1) is one such function
--   - encoding: F′(γ) = 0 when γ determines a single value of the bit b (section c) → the term of γ is 0 when q γ = 0; reason: a transcript with p γ > 0 determines b exactly when it cannot occur under commit(1), i.e. q γ = 0; a transcript with p γ = 0 carries weight 0
--   - encoding: registers whose number differs between transcripts, in linear superposition → fixed finite types A, B for all transcripts; reason: unused registers are padded in the fixed state |0⟩; this changes no probability
--   - reading: correctness: "unveil always return b on |ψb⟩ when both participants are honest" (section c), used on the purified states ψ′1,γ ("then continue with the honest unveil") → hypothesis: the effect acc γ accepts ψ1 γ with probability 1 whenever q γ ≠ 0; reason: honest Alice's unveil acts on her own registers, so keeping her private registers (commit′) instead of decohering them does not change Bob's verdict; correctness is meaningful only for transcripts that can occur under commit(1)
--   - reading: the expected value of F′(γ) under commit′ → the expectation under the transcript law p of a commitment to 0; reason: in commit′ Alice chooses b = 0, and the transcript law of commit′ equals that of the honest commitment to 0 ("formally identical"); this is also the bound needed for the cheating probability, which is an expectation under the same law
--   - encoding: the fidelity [9] (Jozsa) F(ρ, σ) = (Tr √(√ρ σ √ρ))² → QAlgorithms.rootFidelity ρ σ ^ 2; reason: rootFidelity is Tr √(√ρ σ √ρ); its square is Jozsa's fidelity, the one the paper cites
--   - encoding: H_A ⊗ H_B with Alice's side H_A → EuclideanSpace ℂ (A × B) with Alice's side the first factor A; traceLeft gives Bob's reduced state and Alice acts by Matrix.kronecker U 1; reason: fixed ordering convention of the published traceLeft; it changes no instance
-- source:
--   Mayers, Unconditionally secure quantum bit commitment is impossible, arXiv:quant-ph/9605044v2, section e, third step, p.4 ("Alice can change the bit b that she unveils to Bob from 0 to 1 with a probability that goes to 1 as the expected value of F′(γ) goes to 1")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_MayersQBC_expectedFidelity
import Definitions.Def_MayersQBC_cheatProb
open QAlgorithms

namespace MayersQBC

/-- Mayers, arXiv:quant-ph/9605044v2, section e, third step, p.4: "This means that Alice can
change the bit b that she unveils to Bob from 0 to 1 with a probability that goes to 1 as the
expected value of F′(γ) goes to 1", for one value of the security parameter. Let `Γ` be the
finite set of transcripts, `p` their law when Alice commits to `0` and `q` their law when she
commits to `1`; let `ψ0 γ, ψ1 γ` be the unit vectors `ψ′_{0,γ}, ψ′_{1,γ}` of `A ⊗ B` after commit′,
and `acc γ` the effect "the honest unveil of `1` returns `1`", which accepts `ψ1 γ` with certainty
whenever `γ` can occur under a commitment to `1` (`q γ ≠ 0`, correctness). Then there are
unitaries `U γ` on Alice's side such that Alice's cheating probability (apply `U γ`, then unveil
`1` honestly) satisfies `E_γ F′(γ) ≤ Σ_γ p(γ) p_γ ≤ 1`.

**Formalization Note.** See `expectedFidelity` and `cheatProb`: Alice is the first tensor
factor, `F′` is Jozsa's fidelity of Bob's reduced states with `F′(γ) = 0` when `q γ = 0`. The
upper bound `≤ 1` is part of the statement; it is what turns the lower bound into a limit. -/
theorem cheatProb_ge_expectedFidelity {Γ A B : Type} [Fintype Γ] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (p q : Γ → ℝ) (hp : (∀ γ, 0 ≤ p γ) ∧ ∑ γ, p γ = 1)
    (ψ0 ψ1 : Γ → EuclideanSpace ℂ (A × B)) (h0 : ∀ γ, IsState (ψ0 γ)) (h1 : ∀ γ, IsState (ψ1 γ))
    (acc : Γ → Matrix (A × B) (A × B) ℂ) (hacc : ∀ γ, IsEffect (acc γ))
    (hcorrect : ∀ γ, q γ ≠ 0 → effectProb (acc γ) (pureDensity (ψ1 γ)) = 1) :
    ∃ U : Γ → Matrix A A ℂ, (∀ γ, U γ ∈ Matrix.unitaryGroup A ℂ) ∧
      expectedFidelity p q ψ0 ψ1 ≤ cheatProb p acc U ψ0 ∧ cheatProb p acc U ψ0 ≤ 1 := by sorry

end MayersQBC
