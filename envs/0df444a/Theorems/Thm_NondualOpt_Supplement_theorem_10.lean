-- Prove2me | Theorems.Thm_NondualOpt_Supplement_theorem_10
-- name    : NondualOpt.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:16:16.399842+00:00
-- url     : https://prove2.me/theorems/2a53c06c-0cef-47e4-8994-d355768aec8c
-- title:
--   Theorem 10 — iid convex-hull approximation: $\mathrm{fat}$ bounds on $\mathrm{ConvDist}^{\mathrm{wc}}_{X,H,T}$
-- statement:
--   Let $X,H\subseteq\mathbb R^d$ be origin-symmetric convex bodies, $T\ge2$ an integer, $\Lambda=\Lambda_{X,H}=\sup_{g\in H,u\in X}|\langle g,u\rangle|$, and $\mathrm{fat}^{X,H}_\eta=\mathrm{fat}_\eta(L_{X,H})$ the fat-shattering dimension of the class $L_{X,H}=\{H\ni g\mapsto\langle g,u\rangle:u\in X\}$. There are universal constants $C,c,\gamma>0$ such that
--   $$
--   \sup_{\alpha>0}\frac{\alpha}{8}\Big(\frac{\mathrm{fat}^{X,H}_\alpha}{T}\wedge1\Big)\ \le\ \mathrm{ConvDist}^{\mathrm{wc}}_{X,H,T}\ \le\ \inf_{0<\alpha\le\Lambda}\Big\{C\alpha+\frac{C}{T}\Big[\Lambda+\int_\alpha^\Lambda\mathrm{fat}^{X,H}_{c\beta}\log^\gamma\Big(\frac{eT\Lambda}{\beta}\Big)\,d\beta\Big]\Big\}.
--   $$
--   Here $\mathrm{ConvDist}^{\mathrm{wc}}_{X,H,T}$ is the worst case, over distributions supported in $H$, of the expected polar-norm distance from the mean to the convex hull of $T$ iid samples.
--
--   This is the iid counterpart of Theorem 6: with iid linear losses the online-reduction term becomes a static convex-hull approximation problem, and the bounds depend on $\mathrm{fat}$ instead of $\mathrm{sfat}$.
--
--   **Formalization Note** The constants are fixed before $d,X,H,T$; values are extended nonnegative reals and the integral is a Lebesgue integral over $(\alpha,\Lambda]$.
--
--   Differences from the source:
--   - encoding: $\sup_{\alpha>0}(\dots)\le\mathrm{ConvDist}^{\mathrm{wc}}\le\inf_{0<\alpha\le\Lambda}\{\dots\}$ → the lower bound for every $\alpha>0$ and the upper bound for every $0<\alpha\le\Lambda$; reason: equivalent forms of a supremum and an infimum bound
--   - encoding: origin-symmetric convex bodies $X,H\subseteq\mathbb R^d$ → compact, convex, with nonempty interior, and $x\in X\Rightarrow -x\in X$ (same for $H$); reason: the definition of an origin-symmetric convex body
--   - encoding: $\mathrm{ConvDist}^{\mathrm{wc}}$ real valued, $\operatorname{supp}(P)\subseteq H$ → value in $[0,\infty]$, supremum over Borel probability measures with $P(H^c)=0$, expectation a Lebesgue integral of a nonnegative function; reason: $H$ is closed, so $P(H^c)=0$ iff $\operatorname{supp}(P)\subseteq H$; the distance is nonnegative and bounded, so the values agree
--   - encoding: $\int_\alpha^\Lambda\mathrm{fat}_{c\beta}\log^\gamma(eT\Lambda/\beta)\,d\beta$ → lower Lebesgue integral over $(\alpha,\Lambda]$ in $[0,\infty]$, $\mathrm{fat}$ as an extended natural number; reason: the integrand is nonnegative; an infinite $\mathrm{fat}$ makes both sides infinite, as in the paper
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Theorem 10, p.13 (standing assumption of §5.1, p.13)

import Mathlib
import Definitions.Def_NondualOpt_dotPair
import Definitions.Def_NondualOpt_crossDuality
import Definitions.Def_NondualOpt_linClass
import Definitions.Def_NondualOpt_Supplement_fat
import Definitions.Def_NondualOpt_Supplement_convDistWC

open scoped ENNReal

namespace NondualOpt.Supplement

/-- **Theorem 10 (iid convex-hull approximation).** Let `X, H ⊆ ℝ^d` be origin-symmetric convex
bodies, `T ≥ 2`, `Λ = Λ_{X,H}` and `fat^{X,H}_η = fat_η(L_{X,H})`. There are universal constants
`C, c, γ > 0` such that
`sup_{α > 0} (α/8)(fat^{X,H}_α/T ∧ 1) ≤ ConvDist^wc_{X,H,T} ≤
inf_{0 < α ≤ Λ} {Cα + (C/T)[Λ + ∫_α^Λ fat^{X,H}_{cβ} log^γ(eTΛ/β) dβ]}`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Theorem 10, p.13 (standing assumption of
§5.1, p.13: `X, H ⊆ ℝ^d` origin-symmetric convex bodies).

**Formalization Note.** (i) The constants are chosen before `d`, `X`, `H` and `T`. (ii) A convex
body is a compact convex set with nonempty interior; origin symmetry is `x ∈ X → −x ∈ X`.
(iii) The pairing is the published dot product `dotPair d`, `Λ` the published `crossDuality`,
`L_{X,H}` the published `linClass` (functions on `H`), and `fat` uses the margin `α/2` of
Definition 1. (iv) The supremum over `α > 0` and the infimum over `0 < α ≤ Λ` are stated for every
such `α`; values in `ℝ≥0∞` (`fat` enters as an extended natural number). (v) The integral is a
lower Lebesgue integral over `(α, Λ]`. -/
theorem theorem_10 :
    ∃ C c γ : ℝ, 0 < C ∧ 0 < c ∧ 0 < γ ∧
      ∀ (d : ℕ) (X H : Set (Fin d → ℝ)),
        IsCompact X → Convex ℝ X → (interior X).Nonempty → (∀ x ∈ X, -x ∈ X) →
        IsCompact H → Convex ℝ H → (interior H).Nonempty → (∀ g ∈ H, -g ∈ H) →
        ∀ T : ℕ, 2 ≤ T →
        (∀ α : ℝ, 0 < α →
          ENNReal.ofReal (α / 8 *
              (min ((fat (linClass (dotPair d) X H) α : ℝ≥0∞) / (T : ℝ≥0∞)) 1).toReal) ≤
            convDistWC X H T) ∧
        (∀ α : ℝ, 0 < α → α ≤ crossDuality (dotPair d) X H →
          convDistWC X H T ≤
            ENNReal.ofReal (C * α + C / T * crossDuality (dotPair d) X H) +
              ENNReal.ofReal (C / T) * ∫⁻ β in Set.Ioc α (crossDuality (dotPair d) X H),
                (fat (linClass (dotPair d) X H) (c * β) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.log (Real.exp 1 * T * crossDuality (dotPair d) X H / β) ^ γ)) := by sorry

end NondualOpt.Supplement
