-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
-- name    : ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/98ed7cc0-8ae1-5c77-9b65-c245eb5d9113
-- title:
--   Degree inequality for reduced q-expansion function fields
-- statement:
--   Fix a field $L$ of characteristic zero (an algebra over $\mathbb{Q}$), a valuation subring $A \subseteq L$, a field $k$, a ring homomorphism $\pi \colon A \to k$, and an arbitrary subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$. For a field $K$ write $F_K(\Gamma) =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $K((q))$ generated over $K$ by all quotients $\overline{p_f}/\overline{p_g}$, where $f,g$ are modular forms of one and the same integral weight for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, $p_f,p_g \in \mathbb{Z}[[q]]$ are integral $q$-expansions of $f$ and $g$, the bar denotes coefficientwise reduction into $K((q))$, and $\overline{p_g} \neq 0$; and let $F =$ [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)`](def/ModularCurve_LaurentCoeff.html#L103) be the subfield of $L((q))$ generated over $L$ by the coefficientwise image of $F_{\mathbb{Q}}(\Gamma)$. Assume $F$ contains an element $t$ transcendental over $L$ with $F$ finite over $L(t)$. Let $a,b \in \mathbb{Z}[[q]]$, let $X \in F$ have underlying Laurent series $\bar a/\bar b$ over $L$, let $x \in F_k(\Gamma)$ have underlying Laurent series $\bar a/\bar b$ over $k$, and assume $x$ is transcendental over $k$. Then $F_k(\Gamma)$ is finite over $k(x)$ and $[F_k(\Gamma):k(x)] \le [F:L(X)]$, the ranks being `Module.finrank`. The valuation subring $A$ and the map $\pi$ enter only as data: no hypothesis relates them to $a$, $b$, $X$ or $x$, the comparison between the two characteristics being carried entirely by the shared pair of integral power series.
--
--   This is the elementary half of Deuring's theory of reduction of a function field of one variable with respect to a place of its constant field, in the concrete $q$-expansion presentation used for modular curves: the inequality requires no integral model and no good-reduction hypothesis. It is used in the comparisons of degrees and indices for the $q$-expansion function fields of $\Gamma_0(M)$ and $\Gamma_H$, and in the study of the reduction of $q$-expansions modulo a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    {k : Type*} [Field k] (π : A →+* k)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ t : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
      Transcendental L t ∧
        FiniteDimensional
          (IntermediateField.adjoin L
            ({t} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (a b : PowerSeries ℤ)
    (X : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hX : (X : LaurentSeries L) = ModularCurve.intSeriesC L a / ModularCurve.intSeriesC L b)
    (x : ModularCurve.qExpFunctionFieldC k Γ)
    (hx : (x : LaurentSeries k) = ModularCurve.intSeriesC k a / ModularCurve.intSeriesC k b)
    (htr : Transcendental k x) :
    FiniteDimensional (IntermediateField.adjoin k ({x} : Set (ModularCurve.qExpFunctionFieldC k Γ)))
        (ModularCurve.qExpFunctionFieldC k Γ) ∧
      Module.finrank (IntermediateField.adjoin k ({x} : Set (ModularCurve.qExpFunctionFieldC k Γ)))
          (ModularCurve.qExpFunctionFieldC k Γ) ≤
        Module.finrank
          (IntermediateField.adjoin L
            ({X} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by sorry
