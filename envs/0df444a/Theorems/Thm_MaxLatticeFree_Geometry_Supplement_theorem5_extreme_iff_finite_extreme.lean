-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_Supplement_theorem5_extreme_iff_finite_extreme
-- name    : MaxLatticeFree.Geometry.Supplement.theorem5_extreme_iff_finite_extreme
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:03:32.667498+00:00
-- url     : https://prove2.me/theorems/49b7b4b6-4970-4fa0-a807-4920e0aa10b0
-- title:
--   Theorem 5 — B = P + L, and ψ_B is extreme for R_f(ℝ^q) iff ∑_{j≤k} s_j ≥ 1 is extreme for the finite problem
-- statement:
--   Let $f\in\mathbb R^q$ and let $B$ be a maximal lattice-free convex set in $\mathbb R^q$ with $f$ in its interior. Let $L=\operatorname{lin}(B)$ be the lineality space of $B$ and $P=B\cap(f+L^\perp)$. Then:
--
--   1. $L$ is a linear subspace and $B=P+L$;
--   2. $L$ is a rational space;
--   3. $P$ is a polytope;
--   4. for every listing $v^1,\dots,v^k$ of the vertices of $P$ (each once) and every basis $r^{k+1},\dots,r^{k+h}$ of $L$ with rational coordinates, putting $r^j=v^j-f$ for $j\le k$,
--
--   $$
--   \sum_{r\in\mathbb R^q}\psi_B(r)s_r\ge1 \text{ is extreme for } R_f(\mathbb R^q)\iff \sum_{j=1}^ks_j\ge1 \text{ is extreme for } \operatorname{conv}\big(R_f(r^1,\dots,r^{k+h})\big).
--   $$
--
--   Extremality is that of p. 7: a valid inequality is extreme when it is not dominated, coefficientwise, by the average of two distinct valid inequalities with the same right-hand side; for the finite problem the coefficient vector of $\sum_{j\le k}s_j\ge1$ is $1$ on the vertex directions and $0$ on the basis directions of $L$.
--
--   The theorem reduces extremality of an infinite-model inequality to a finite check on the vertices of $P$ and a rational basis of $L$, a correspondence close to a result of Dey and Wolsey.
--
--   **Formalization Note** $\psi_B$ is the published `psiB f ⊤ B` $=\rho_{B-f}$ ($W=\mathbb R^q$ is `⊤`). The lineality space is the published `linSpace B`; the theorem asserts a submodule with that carrier. "Vertices" are the extreme points of $P$, enumerated injectively; a rational basis is a linearly independent spanning family of $L$ with rational coordinates. All $k+h$ variables of the finite relaxation are nonnegative. The cases $h=0$ (bounded $B$) and any $k$ are included; no rationality of $f$ or of $B$ is assumed.
--
--   Differences from the source:
--   - reading: the inequality ∑_{j=1}^k s_j ≥ 1 is extreme for conv(R_f(r^1, …, r^{k+h})), extremality defined on p. 7 only for R_f(W) → IsExtremeFinite: the p. 7 definition applied to coefficient vectors in ℝ^{k+h}, with coefficients 1 on the first k and 0 on the last h; reason: this is how the proof on p. 24 uses it (vectors α, β with ½(α_j + β_j) ≤ ψ_B(r^j))
--   - reading: ψ_B(r) = max_i a_i r for a row description of B (4) → the published psiB = ρ_{B−f}; reason: (4) depends on the description when it has non-tight rows; ρ_{B−f} equals (4) for every tight description (Remark 29)
--   - encoding: v^1, …, v^k the vertices of P; r^{k+1}, …, r^{k+h} a rational basis of L; L = lin(B) → every injective enumeration of the extreme points of P, every linearly independent spanning family of L with rational coordinates; a submodule L with carrier linSpace B; reason: the theorem holds for every choice, which is how the page's 'Let' is read; same instances
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 7, Theorem 5 (extremality defined on p. 7)

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Inequalities_Polar
import Definitions.Def_MaxLatticeFree_Geometry_recCone
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_Rational
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_FiniteModel
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_Extreme

open Pointwise
open MaxLatticeFree.Inequalities

namespace MaxLatticeFree.Geometry.Supplement

theorem theorem5_extreme_iff_finite_extreme {q : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (B : Set (EuclideanSpace ℝ (Fin q))) (hB : IsMaximalLatticeFree f ⊤ B)
    (hf : f ∈ intRel (affSpace f ⊤) B) :
    ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin q)),
      (L : Set (EuclideanSpace ℝ (Fin q))) = linSpace B ∧
      B = (B ∩ (f +ᵥ (Lᗮ : Set (EuclideanSpace ℝ (Fin q))))) +
        (L : Set (EuclideanSpace ℝ (Fin q))) ∧
      IsRationalSubspace L ∧
      IsPolytope (B ∩ (f +ᵥ (Lᗮ : Set (EuclideanSpace ℝ (Fin q))))) ∧
      ∀ (k h : ℕ) (v : Fin k → EuclideanSpace ℝ (Fin q)) (b : Fin h → EuclideanSpace ℝ (Fin q)),
        Function.Injective v →
        Set.range v = Set.extremePoints ℝ (B ∩ (f +ᵥ (Lᗮ : Set (EuclideanSpace ℝ (Fin q))))) →
        LinearIndependent ℝ b → Submodule.span ℝ (Set.range b) = L →
        (∀ j i, ∃ c : ℚ, (b j).ofLp i = (c : ℝ)) →
        (IsExtreme f ⊤ (psiB f ⊤ B) ↔
          IsExtremeFinite (convexHull ℝ (RfFinite f (Fin.append (fun j => v j - f) b)))
            (Fin.append (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)))) := by sorry

end MaxLatticeFree.Geometry.Supplement
