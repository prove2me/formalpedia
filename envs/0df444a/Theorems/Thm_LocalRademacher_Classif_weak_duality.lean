-- Prove2me | Theorems.Thm_LocalRademacher_Classif_weak_duality
-- name    : LocalRademacher.Classif.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:47:44.81884+00:00
-- url     : https://prove2.me/theorems/0de21970-bc0a-4fff-b8f1-b3dfdf60ea46
-- title:
--   Proof of Theorem 6.3, p. 30 — weak duality: min{Pₙℓ(f(X),σ) : Pₙℓ(f(X),Y) ≤ 2r/α²} ≥ g(μ) = min_f L(f, μ) for μ ≥ 0
-- statement:
--   Let $X_1,\dots,X_n$ be fixed inputs ($n\ge1$) with labels $Y_i\in\{-1,1\}$, let $\mathcal F$ be a class of $\{-1,1\}$-valued classifiers, $\ell$ the discrete loss and $P_n\ell(f(X),z)=\frac1n\sum_i\ell(f(X_i),z_i)$. Fix a sign vector $\sigma\in\{-1,1\}^n$, reals $r$ and $\alpha>0$, and $\mu\ge0$, and suppose some $f\in\mathcal F$ has $P_n\ell(f(X),Y)\le 2r/\alpha^2$. Put
--   $$L(f,\mu)=P_n\ell(f(X),\sigma)+\mu\Big(P_n\ell(f(X),Y)-\frac{2r}{\alpha^2}\Big),\qquad g(\mu)=\min_{f\in\mathcal F}L(f,\mu).$$
--   Then
--
--   1. every $f\in\mathcal F$ with $P_n\ell(f(X),Y)\le 2r/\alpha^2$ satisfies $P_n\ell(f(X),\sigma)\ge L(f,\mu)$;
--   2. $$\min\Big\{P_n\ell(f(X),\sigma) : f\in\mathcal F,\ P_n\ell(f(X),Y)\le\frac{2r}{\alpha^2}\Big\}\ge g(\mu).$$
--
--   This is the Lagrangian weak-duality step of the proof of Theorem 6.3: the constraint $P_n\ell_f\le 2r/\alpha^2$ is moved into the objective with multiplier $\mu$, and the constrained minimum is bounded below by the unconstrained minimum of the Lagrangian over the whole class.
--
--   **Formalization Note** The feasibility hypothesis is added because the page's $\min$ presupposes a nonempty feasible set. Both minima are Lean's real infima over subtypes; the feasible $f$ makes them nonempty and the losses are bounded, so they are true minima.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Proof of Theorem 6.3, p. 30, second and third displays

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting

namespace LocalRademacher.Classif

/-- **Weak duality** in the proof of Theorem 6.3 (Bartlett, Bousquet & Mendelson,
arXiv:math/0508275v1, p. 30). Fix a sign vector `σ`, `α > 0` and `μ ≥ 0`, and suppose some
`f ∈ F` has `Pₙℓ(f(X), Y) ≤ 2r/α²`. Then (1) every such `f` satisfies
`Pₙℓ(f(X), σ) ≥ L(f, μ) := Pₙℓ(f(X), σ) + μ (Pₙℓ(f(X), Y) − 2r/α²)`, and (2)
`min{Pₙℓ(f(X), σ) : f ∈ F, Pₙℓ(f(X), Y) ≤ 2r/α²} ≥ g(μ) := min_{f ∈ F} L(f, μ)`. -/
theorem weak_duality {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (σ : Fin n → Bool) (r α : ℝ) (hα : 0 < α) (μ : ℝ) (hμ : 0 ≤ μ)
    (hfeas : ∃ f ∈ F, empLoss xs ys f ≤ 2 * r / α ^ 2) :
    (∀ f ∈ F, empLoss xs ys f ≤ 2 * r / α ^ 2 →
        empLoss xs (UnderstandingML.signVec σ) f ≥
          empLoss xs (UnderstandingML.signVec σ) f + μ * (empLoss xs ys f - 2 * r / α ^ 2)) ∧
      (⨅ f : {f : X → ℝ // f ∈ F ∧ empLoss xs ys f ≤ 2 * r / α ^ 2},
          empLoss xs (UnderstandingML.signVec σ) f.1) ≥
        ⨅ f : F, (empLoss xs (UnderstandingML.signVec σ) f.1
          + μ * (empLoss xs ys f.1 - 2 * r / α ^ 2)) := by sorry

end LocalRademacher.Classif
