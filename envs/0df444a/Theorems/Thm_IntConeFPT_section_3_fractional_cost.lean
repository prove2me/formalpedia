-- Prove2me | Theorems.Thm_IntConeFPT_section_3_fractional_cost
-- name    : IntConeFPT.section_3_fractional_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:56.46024+00:00
-- url     : https://prove2.me/theorems/238f677a-ec6a-49a4-9280-d36953ae7c7f
-- title:
--   §3, (3.1a)–(3.1b) — $P_r=\operatorname{conv}(V_r)$, finite LP value, and $\Phi_r$ is the support function of $D_r$
-- statement:
--   There is a constant $C$ such that for every valid instance, type $t$ and residue $r$:
--
--   1. $V^{(t)}_r$ is finite, and each of its points $(x,u)$ has rational $u$, with encoding length of $(x,u)$ at most $|I|^C$;
--   2. every $(x,u)\in S^{(t)}_r$ is a convex combination of points of $V^{(t)}_r$ with the same integer block $x$;
--   3. $P^{(t)}_r=\operatorname{conv}(V^{(t)}_r)$;
--   4. for $(z,w,n)\in C^{(t)}_r$, the minimal fractional cost over representations by all of $S^{(t)}_r$ equals $\Phi^{(t)}_r(z,w,n)$, and this value is attained by a representation on $V^{(t)}_r$;
--   5. $D^{(t)}_r\ne\emptyset$;
--   6. for every $(z,w,n)\in\mathbb R^{d+k+1}$,
--   $$
--   \Phi^{(t)}_r(z,w,n)=\sup_{(a,b)\in D^{(t)}_r}\big(\langle a,(z,w)\rangle+bn\big);
--   $$
--   7. the epigraph $\{((z,w,n),s):\Phi^{(t)}_r(z,w,n)\le s\}$ is the solution set of finitely many linear inequalities with rational coefficients, so $\Phi^{(t)}_r$ is closed, convex and rational polyhedral.
--
--   These facts make (3.2e) a rational polyhedral constraint and let the separation oracle of Lemma 13 cut with dual solutions.
--
--   **Formalization Note** $\Phi^{(t)}_r$ is `Instance.Phi`, valued in `EReal`; the supremum in item 6 is taken in `EReal`.
--
--   Differences from the source:
--   - encoding: Φ_r^(t) = +∞ outside C_r^(t); value of the finite LP (3.1a) → Φ in EReal, the infimum over fractional representations by V_r (⊤ if there is none); reason: the paper sets Φ = +∞ outside C_r; on C_r the infimum is the LP value
--   - encoding: P_r^(t) = conv(V_r^(t)) is a rational polytope → V_r finite with rational points, and P_r = convexHull ℝ V_r; reason: a rational polytope is the convex hull of finitely many rational points
--   - encoding: Φ_r^(t) is closed, convex and rational polyhedral → its epigraph is the solution set of finitely many rational linear inequalities; reason: definition of a rational polyhedral function; closedness and convexity follow
--   - encoding: its points have polynomial encoding length → ∃ C before all instances with (encGen x u).length ≤ (encInstance I).length ^ C; reason: reading of "polynomial" with one absolute exponent
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - encoding: r ∈ {0, …, 2^d − 1}^d → r : Fin d → Fin (2^d) (Residue d); reason: Lean convention; same residues
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §3, pp.8–9, (3.1a), (3.1b)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

/-- **§3, (3.1a)–(3.1b): fiber vertices, `P_r = conv(V_r)`, and `Φ_r` as the support function of
`D_r`.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), §3, pp.8–9: "There are finitely many possible integer vectors
x, and each fiber has finitely many vertices, so V_r^(t) is finite. … Every generator in S_r^(t) is
a convex combination of points of V_r^(t) with the same integer coordinates and hence the same
cost. In particular, P_r^(t) = conv(V_r^(t)) is a rational polytope. Therefore, the minimal
fractional cost of (z, w, n) equals the value of the finite linear program (3.1a). … D_r^(t) … is a
nonempty rational polyhedron … For every (z, w, n) ∈ C_r^(t), the primal LP is feasible and has a
finite optimal value, so strong duality gives Φ_r^(t)(z, w, n) = sup_{(a,b)∈D_r^(t)} (⟨a, (z, w)⟩ + bn).
Outside C_r^(t), the primal is infeasible and the dual, being feasible, is unbounded above. Thus
this identity holds throughout R^{d+k+1}, and Φ_r^(t) is the support function of D_r^(t).
Consequently, it is closed, convex, and rational polyhedral."

There is an absolute constant `C` such that for every valid instance, type `t` and residue `r`:
1. `V_r` is finite, and its points are rational with encoding length at most `|I|^C`;
2. every generator of `S_r` is a convex combination of points of `V_r` with the same `x`;
3. `P_r = conv(V_r)`;
4. on `C_r`, the minimal fractional cost over representations by all of `S_r` equals `Φ_r`, and
   `Φ_r` is attained by a representation on `V_r` (so it is finite);
5. `D_r` is nonempty;
6. `Φ_r(ξ) = sup_{(a,b)∈D_r} (⟨a, (z, w)⟩ + b n)` for every `ξ = (z, w, n)`;
7. the epigraph `{(ξ, s) : Φ_r(ξ) ≤ s}` is the solution set of finitely many linear inequalities
   with rational coefficients (closed, convex, rational polyhedral).

**Formalization Note.** `Φ_r` takes values in `EReal` (`⊤` outside `C_r`). "Polynomial encoding
length" is read as `(encGen x u).length ≤ |I|^C` with one absolute `C` placed before the instance. -/
theorem section_3_fractional_cost :
    ∃ C : ℕ, ∀ I : Instance, I.Valid → ∀ (t : Fin I.τ) (r : Residue I.d),
    (I.Vr t r).Finite ∧
    (∀ g ∈ I.Vr t r, ∃ q : Fin I.k → ℚ, g.2 = (fun j => (q j : ℝ)) ∧
      (encGen g.1 q).length ≤ (encInstance I).length ^ C) ∧
    (∀ g ∈ I.Sr t r,
      g.toReal ∈ convexHull ℝ (Gen.toReal '' {v | v ∈ I.Vr t r ∧ v.1 = g.1})) ∧
    I.Pr t r = convexHull ℝ (Gen.toReal '' I.Vr t r) ∧
    (∀ ξ ∈ I.Cr t r,
      (⨅ θ ∈ {θ | IsFracRep (I.Sr t r) θ ξ}, ((fracCost (I.f t) θ : ℝ) : EReal)) = I.Phi t r ξ ∧
      ∃ θ, IsFracRep (I.Vr t r) θ ξ ∧ ((fracCost (I.f t) θ : ℝ) : EReal) = I.Phi t r ξ) ∧
    (I.Dr t r).Nonempty ∧
    (∀ ξ : Pt I.d I.k, I.Phi t r ξ =
      ⨆ ab ∈ I.Dr t r, ((pairing ab.1 (ξ.1, ξ.2.1) + ab.2 * ξ.2.2 : ℝ) : EReal)) ∧
    ∃ (m : ℕ) (α : Fin m → (Fin I.d → ℚ) × (Fin I.k → ℚ)) (β η c : Fin m → ℚ),
      ∀ (ξ : Pt I.d I.k) (s : ℝ), I.Phi t r ξ ≤ (s : EReal) ↔
        ∀ i, pairing (ratPair (α i).1 (α i).2) (ξ.1, ξ.2.1) + (β i : ℝ) * ξ.2.2 + (η i : ℝ) * s
          ≤ (c i : ℝ) := by sorry

end IntConeFPT
