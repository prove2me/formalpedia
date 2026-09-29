-- Prove2me | Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
-- name    : ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/db8627ff-d055-576c-ba3d-7cfc7a6eff5f
-- title:
--   Bounded denominators for rational q-expansions on Γ₁(M)
-- statement:
--   Let $M$ be a natural number, assumed nonzero, and let $k$ be an integer. Let $f$ be a modular form of weight $k$ for the subgroup $\Gamma_1(M)$ of $\mathrm{GL}_2(\mathbb{R})$, i.e. for `CongruenceSubgroup.Gamma1 M` viewed as a subgroup of $\mathrm{GL}(\mathrm{Fin}\ 2)(\mathbb{R})$. Assume that the $q$-expansion of $f$ of width $1$ — the expansion in $q = e^{2\pi i \tau}$ given by `UpperHalfPlane.qExpansion 1 f` — has rational coefficients, in the sense that for every natural number $n$ there is $r \in \mathbb{Q}$ with $n$-th coefficient equal to the image of $r$ in $\mathbb{C}$. The conclusion asserts the existence of a nonzero integer $D$ and a formal power series $p \in \mathbb{Z}[[X]]$ such that [`ModularCurve.IsIntegralQExp`](def/ModularCurve_X1.html#L37) holds for the function $(D : \mathbb{C}) \cdot f$ on the upper half-plane together with $p$; by definition this means that the power series obtained from $p$ by applying the ring homomorphism $\mathbb{Z} \to \mathbb{C}$ coefficientwise equals the width-$1$ $q$-expansion of $D \cdot f$. Thus the denominators of the Fourier coefficients of $f$ at $\infty$ are bounded, and some nonzero integer multiple of $f$ has integral $q$-expansion.
--
--   This is the bounded-denominators statement for modular forms on $\Gamma_1(M)$ with rational Fourier expansion at $\infty$: the forms with integral $q$-expansion span, over $\mathbb{Q}$, those with rational $q$-expansion. It underlies the construction of integral structures on spaces of modular and cusp forms used later, and is invoked throughout the treatment of $q$-expansions on modular curves, for instance in producing bases of cusp forms on $\Gamma_1(M)$ whose $q$-coefficients are integral. The proof cites the modularity of the weight-one Eisenstein series attached to the cubic character and a denominator bound for $\Gamma(N)$-invariant functions with rational $q$-coefficients after multiplication by a power of the discriminant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ)) :
    ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp ((D : ℂ) • (⇑f : UpperHalfPlane → ℂ)) p := by sorry
