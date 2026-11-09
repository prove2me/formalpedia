-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_5_2
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:03.399641+00:00
-- url     : https://prove2.me/theorems/5f4ba7bd-0f19-4549-8492-70c7e82d7302
-- title:
--   Lemma 5.2 — the table recurrence
-- statement:
--   Let $b\ge4$, $\theta\in\{0,\dots,2M-1\}$, $\gamma\in(0,1)$. For every cell $C$, boundary vector $x$ and $t\in\{0,\dots,W(C)\}$,
--
--   $$F_C(x,t)=\max_{y,t_0,t_1}\Bigl\{\mathrm{Loc}_C(x,y)+\sum_{j\in\{0,1\}}\Bigl(F_{C_j}(x^{(j)},t_j)+t_j(\Delta U_j-\Delta R_j)+(W(C_j)-t_j)\Delta R_j\Bigr)\Bigr\},$$
--
--   where the maximum ranges over vectors $y$ of allowed counts for the own groups of $C$ and integers $0\le t_j\le W(C_j)$ with $|y|+t_0+t_1=t$. If $C$ is a leaf, the terms for the children are absent ($t_0=t_1=0$). An empty maximum, and any term containing $-\infty$, is $-\infty$.
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: cells as open intervals (ζ, ζ + D) of a binary tree → cells named by heap indices 1 ≤ C < 8M with explicit cellLo, cellLen; groups named by their least vertex; reason: a bijective naming of the same cells and groups; geometry recomputed from the index
--   - encoding: values in ℤ ∪ {−∞} → WithBot ℤ with Finset.sup; ⊥ + a = ⊥; reason: the same extended integers; F_C is the true maximum, not defined by the recurrence
--   - encoding: vectors y indexed by A(C), x by R(C) → functions on group ids, 0 outside A(C) for y; entries of x outside R(C) unused; reason: restriction to the relevant groups recovers the source vectors; the extra coordinates of x are irrelevant, and y has a unique zero extension
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 5.2, PDF p. 20 (printed p. 19); proof to PDF p. 21

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

open Classical

/-- Lemma 5.2: for every cell `C`, boundary vector `x` and `t ∈ {0, …, W(C)}`,
`F_C(x, t) = max_{y, t₀, t₁} {Loc_C(x, y) + Σ_{j ∈ {0,1}} (F_{C_j}(x^{(j)}, t_j) + t_j(ΔU_j − ΔR_j)
+ (W(C_j) − t_j)ΔR_j)}` over own-group vectors `y` of allowed counts and `0 ≤ t_j ≤ W(C_j)` with
`|y| + t₀ + t₁ = t`; at a leaf the children's terms are absent. Maxima are in `WithBot ℤ`. -/
theorem lemma_5_2 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (C : ℕ) (hC : IsCell n C)
    (x : Fin n → ℕ) (hx : IsBoundary P γ C x) (t : ℕ) (ht : t ≤ W P C) :
    F P γ C x t =
      if IsLeaf n C then
        (ownVecs P γ C).sup (fun y =>
          if ysize P C y = t then ((Loc P C x y : ℤ) : WithBot ℤ) else ⊥)
      else
        (ownVecs P γ C ×ˢ (Finset.range (W P (2 * C) + 1) ×ˢ Finset.range (W P (2 * C + 1) + 1))).sup
          (fun z => if ysize P C z.1 + z.2.1 + z.2.2 = t then
              ((Loc P C x z.1 : ℤ) : WithBot ℤ) + childTerm P γ C (2 * C) x z.1 z.2.1 +
                childTerm P γ C (2 * C + 1) x z.1 z.2.2
            else ⊥) := by sorry

end IntervalMaxCutEPTAS.Scheme
