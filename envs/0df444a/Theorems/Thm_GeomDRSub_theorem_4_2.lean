-- Prove2me | Theorems.Thm_GeomDRSub_theorem_4_2
-- name    : GeomDRSub.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:08.182543+00:00
-- url     : https://prove2.me/theorems/da92c069-54bf-47aa-b58c-12974eac8d42
-- title:
--   Theorem 4.2 — geometry-dependent upper-linearizability with coefficient $\alpha(\zeta)$
-- statement:
--   Let $\zeta\in[0,1]$ and let $K\subseteq[0,1]^d$ be nonempty, compact, convex and down-closed with $\zeta\mathbf 1\in K$. Then:
--   1. $h_\zeta(K)\subseteq K$;
--   2. for every nonnegative continuously differentiable DR-submodular $f$ on the cube,
--   $$
--   \alpha(\zeta)f(o)-f\big(h_\zeta(x)\big)\le\alpha(\zeta)\,\big\langle g_\zeta(f,x),\,o-x\big\rangle\qquad(x,o\in K);
--   $$
--   3. hence the class of such $f$, the action $h_\zeta$ and the field $g_\zeta$ are upper-linearizable (Definition 3.2) with $\alpha=\beta=\alpha(\zeta)$;
--   4. the coefficient is nondecreasing on $[0,1]$ and equals
--   $$
--   \alpha(\zeta)=\begin{cases}\dfrac{4(1-\zeta)}{(3-2\zeta)^2},&0\le\zeta\le1/2,\\[4pt] \dfrac12,&1/2\le\zeta\le1,\end{cases}
--   \qquad\alpha(\zeta)=\frac12-\frac{(1-2\zeta)_+^2}{2(3-2\zeta)^2};
--   $$
--   5. consequently $\alpha(0)=4/9$ and $\alpha(\zeta)=1/2$ for $\zeta\ge1/2$.
--
--   This is the structural result behind the online guarantee: the reward deficit of the action $h_\zeta(x)$ against any comparator is bounded by a term linear in $o-x$.
--
--   Differences from the source:
--   - encoding: f : [0,1]^d → ℝ continuously differentiable, gradient continuously extended to the boundary → f : ℝ^d → ℝ with ContDiffOn ℝ 1 f (cube d), gradient = within-cube derivative gradQ; reason: only the values on the cube matter; for d ≥ 1 the within-cube derivative is the continuous extension of the interior gradient
--   - encoding: the action map h : K → K → a map ℝ^d → ℝ^d with h(K) ⊆ K; reason: only its values on K enter (10)
--   - encoding: (35)–(36), properties of the function α on [0,1]; (t)₊ → stated for every level ζ' in the respective range of [0,1]; max t 0; reason: they do not depend on K or on the fixed ζ
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Theorem 4.2, p.14, Eqs. (34)–(36)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_IsAdmissible
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_GeomDRSub_alphaLow
import Definitions.Def_GeomDRSub_hAct
import Definitions.Def_GeomDRSub_field
import Definitions.Def_GeomDRSub_IsUpperLinearizable

namespace GeomDRSub

/-- **Theorem 4.2 (geometry-dependent upper-linearizability).** Aggarwal–Lu, arXiv:2610.00545,
p.14: "Let `K ⊆ [0, 1]^d` be nonempty, compact, convex, and down-closed, with `ζ1 ∈ K`. Then
`h_ζ(K) ⊆ K` and `α(ζ)f(o) − f(h_ζ(x)) ≤ α(ζ)⟨g_ζ(f, x), o − x⟩` `(x, o ∈ K)`, (34) with `α(ζ)` as
defined in (11). In particular, upper-linearizability (Definition 3.2) holds with
`α = β = α(ζ)`. This coefficient is nondecreasing and equals
`α(ζ) = 4(1 − ζ)/(3 − 2ζ)²` for `0 ≤ ζ ≤ 1/2`, `1/2` for `1/2 ≤ ζ ≤ 1`,
`= 1/2 − (1 − 2ζ)₊²/(2(3 − 2ζ)²)`. (35) Consequently, `α(0) = 4/9`, `α(ζ) = 1/2` `(ζ ≥ 1/2)`. (36)"

Conjuncts, in order: `h_ζ(K) ⊆ K`; (34) for every nonnegative DR-submodular `f`; Definition 3.2
with `α = β = α(ζ)` for the class of nonnegative DR-submodular functions; monotonicity of `α` on
`[0,1]`; the two-piece form and the single-formula form of (35) on `[0,1]`; and (36).

**Formalization Note.** `ζ ∈ [0,1]` is the standing "supplied number `ζ ∈ [0,1]`" of p.8, and the
objectives are those of Section 4 (p.10: nonnegative, continuously differentiable on the cube,
satisfying (3)). `(t)₊` is `max t 0`. The closed forms are stated for every level in `[0,1]`. -/
theorem theorem_4_2 {d : ℕ} (ζ : ℝ) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsAdmissible K ζ) :
    (∀ x ∈ K, hAct ζ x ∈ K) ∧
      (∀ f : EuclideanSpace ℝ (Fin d) → ℝ, (∀ y ∈ cube d, 0 ≤ f y) → IsDRSubmodular f →
        ∀ x ∈ K, ∀ o ∈ K,
          alphaLow ζ * f o - f (hAct ζ x) ≤ alphaLow ζ * inner ℝ (field ζ f x) (o - x)) ∧
      IsUpperLinearizable {f | (∀ y ∈ cube d, 0 ≤ f y) ∧ IsDRSubmodular f} K (hAct ζ)
        (field ζ) (alphaLow ζ) (alphaLow ζ) ∧
      MonotoneOn alphaLow (Set.Icc (0 : ℝ) 1) ∧
      (∀ ζ' ∈ Set.Icc (0 : ℝ) (1 / 2), alphaLow ζ' = 4 * (1 - ζ') / (3 - 2 * ζ') ^ 2) ∧
      (∀ ζ' ∈ Set.Icc (1 / 2 : ℝ) 1, alphaLow ζ' = 1 / 2) ∧
      (∀ ζ' ∈ Set.Icc (0 : ℝ) 1,
        alphaLow ζ' = 1 / 2 - (max (1 - 2 * ζ') 0) ^ 2 / (2 * (3 - 2 * ζ') ^ 2)) ∧
      alphaLow 0 = 4 / 9 ∧ (∀ ζ' ∈ Set.Icc (1 / 2 : ℝ) 1, alphaLow ζ' = 1 / 2) := by sorry

end GeomDRSub
