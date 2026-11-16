-- Prove2me | Theorems.Thm_MatSemiBurnside_Supplement_theorem_4
-- name    : MatSemiBurnside.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:47:44.773204+00:00
-- url     : https://prove2.me/theorems/867a6586-e00d-4373-aff9-8cac8b43b861
-- title:
--   Theorem 4: homogeneous ABPs $\mathcal A_{w,d}$ are not Zariski closed ($w\ge2$, $d\ge3$, $m\ge2w+7$)
-- statement:
--   Let $w\ge2$, $d\ge3$ and $m\ge2w+7$. Let $\mathcal A_{w,d}\subseteq\overline{\mathbb Q}[x_1,\dots,x_m]_d$ be the set of polynomials $L_1(x)\cdots L_d(x)$ computed by homogeneous algebraic branching programs of width $w$ and degree $d$ ($L_1$ is $1\times w$, $L_d$ is $w\times1$, the others $w\times w$, all entries homogeneous linear forms with coefficients in $\overline{\mathbb Q}$), and let $\overline{\mathcal A_{w,d}}$ be its Zariski closure in the coefficient space of $\overline{\mathbb Q}[x]_d$. Then $\mathcal A_{w,d}$ is separated from its closure:
--   $$\overline{\mathcal A_{w,d}}\setminus\mathcal A_{w,d}\neq\emptyset .$$
--
--   So for every fixed width $w\ge2$ and degree $d\ge3$ there are polynomials approximable by width-$w$ homogeneous ABPs that no such ABP computes exactly, once there are at least $2w+7$ variables.
--
--   **Formalization Note** The statement asserts the existence of some $f\in\overline{\mathcal A_{w,d}}$ with $f\notin\mathcal A_{w,d}$; the explicit witness $F_{w,d}$ of the proof is not named.
--
--   Differences from the source:
--   - encoding: "A_{w,d} is separated from A‾_{w,d}" → ∃ f ∈ A‾_{w,d} with f ∉ A_{w,d}; reason: the meaning given on p.5 ("implying that F_{w,d} ∈ A‾_{w,d} ∖ A_{w,d}")
--   - encoding: width "at most w", "width-w" → exactly w columns, zero forms allowed; reason: an ABP of smaller width is padded with zero forms to width w, so the sets coincide
--   - encoding: Zariski closure in the vector space ℚ̄[x]_d of coefficient vectors → zero set in ℚ̄[x]_d of the polynomial functions of the coefficient vector (variables indexed by all monomials) vanishing on A_{w,d}; reason: coordinates of monomials of degree ≠ d vanish on ℚ̄[x]_d, so the same closed set
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 4, p.5 (restated identically pp.16 and 40; ABPs defined pp.4–5 and §4.1, p.16; proof Appendix F, pp.40–47)

import Mathlib
import Definitions.Def_MatSemiBurnside_Supplement_ABPSet
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

/-- **Theorem 4.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 4, p.5 (restated identically pp.16 and 40; proof App. F, pp.40–47):
"Let w ≥ 2 and d ≥ 3 and m ≥ 2w+7. The class A_{w,d} of width-w degree-d homogenous ABPs is separated from
A‾_{w,d}."; p.5: "… implying that F_{w,d} ∈ A‾_{w,d} ∖ A_{w,d}".

**Formalization Note.** "Separated from its closure" is stated as: some polynomial lies in the Zariski closure
A‾_{w,d} (taken in the coefficient space of ℚ̄[x₁, …, x_m]_d, `coeffZariskiClosure`) but not in A_{w,d}
(`ABPSet`, linear forms with ℚ̄ coefficients). The explicit witness F_{w,d} of the proof is not named. -/
theorem theorem_4 (w d m : ℕ) (hw : 2 ≤ w) (hd : 3 ≤ d) (hm : 2 * w + 7 ≤ m) :
    ∃ f ∈ coeffZariskiClosure d (ABPSet m w d), f ∉ ABPSet m w d := by sorry

end MatSemiBurnside.Supplement
