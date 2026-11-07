-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_3
-- name    : IterRoundDet.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:25.500196+00:00
-- url     : https://prove2.me/theorems/8f446a16-9b6e-4ee8-8a9d-7fa89105e3d3
-- title:
--   Lemma 3.3 — the penalty form (15), (16); $f$ is concave (its last sentence is Proposition C.5)
-- statement:
--   For $(a,x)\in\mathcal R$,
--
--   $$f(a,x)=\inf_{\theta\in\mathbb R^n}\{\log p(x\circ e^\theta)-\theta\cdot a\}=\inf_{\theta\in\mathbb R^n}\{\log p(e^\theta)-\theta\cdot a\}+\sum_i a_i\log x_i.$$
--
--   Additionally, $f$ is a concave function of $(a,x)$ on $\mathcal R$, and the inner minimization over $\theta$ is a convex problem. These facts make the relaxation a concave program.
--
--   **Formalization Note** The real infima are stated together with their lower bounds. The lemma's closing sentence, that the maximum "can be optimized in polynomial time", is stated in its precise form as Proposition C.5.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - encoding: the sentence that REL can be optimized in polynomial time → stated as the separate item IterRoundDet.proposition_C_5; reason: the paper gives the precise form there, with its machine clauses; the title says so
--   - generalization: (15) and the concavity of f → also (16), and that the families whose infima are f, (16) and (15) are bounded below; reason: (16) is proved in the lemma's proof on the same page, and boundedness below holds on R, where f is finite (Lemma 3.4); the printed claims are conjuncts, so the item specializes to the lemma
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.3, (15), and (16) of its proof, p.13

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.3, (15), with (16) from its proof, p.13. For `(a, x) ∈ R`,
`f(a, x) = inf_θ {log p(e^θ) − θ·a} + ∑_i a_i log x_i`. Additionally `f` is concave in `(a, x)`, and the inner
minimization over `θ` is a convex problem.

**Formalization Note.** The infima are real infima, so each comes with `BddBelow`. A term with
`a_i = x_i = 0` is `0 · log 0 = 0`. The lemma's last sentence ("can be optimized in polynomial time") is stated
in its precise form as Proposition C.5, `proposition_C_5`. Concavity on the set `R` includes its convexity. -/
theorem lemma_3_3 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c) {M : Matroid (Fin n)}
    (hM : M.E = Set.univ) :
    (∀ a x, Feasible c M a x →
      BddBelow (Set.range fun θ : {θ : Fin n → ℝ // 0 ≤ a ⬝ᵥ θ} =>
        Real.log (pEval c fun i => x i * Real.exp ((θ : Fin n → ℝ) i))) ∧
      BddBelow (Set.range fun θ : Fin n → ℝ =>
        Real.log (pEval c fun i => x i * Real.exp (θ i)) - θ ⬝ᵥ a) ∧
      BddBelow (Set.range fun θ : Fin n → ℝ =>
        Real.log (pEval c fun i => Real.exp (θ i)) - θ ⬝ᵥ a) ∧
      relaxObj c a x =
        ⨅ θ : Fin n → ℝ, (Real.log (pEval c fun i => x i * Real.exp (θ i)) - θ ⬝ᵥ a) ∧
      relaxObj c a x =
        (⨅ θ : Fin n → ℝ, (Real.log (pEval c fun i => Real.exp (θ i)) - θ ⬝ᵥ a)) +
          ∑ i, a i * Real.log (x i)) ∧
    ConcaveOn ℝ {p : (Fin n → ℝ) × (Fin n → ℝ) | Feasible c M p.1 p.2}
      (fun p => relaxObj c p.1 p.2) ∧
    (∀ a : Fin n → ℝ, ConvexOn ℝ Set.univ fun θ : Fin n → ℝ =>
      Real.log (pEval c fun i => Real.exp (θ i)) - θ ⬝ᵥ a) := by sorry

end IterRoundDet
