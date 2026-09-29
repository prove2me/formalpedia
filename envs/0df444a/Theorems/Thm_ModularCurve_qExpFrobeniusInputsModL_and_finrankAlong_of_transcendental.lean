-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
-- name    : ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/e1ff95e0-91d4-5738-be22-c5e219e6a6d7
-- title:
--   Frobenius inputs and degree ℓ for ̄ F/Frob(̄ F)
-- statement:
--   Let $K$ be an algebraically closed field of prime characteristic $\ell$ and let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Write $\bar F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $K \subseteq K((q)) =$ `LaurentSeries K` generated over $K$ by the set `intFormRatiosC K Γ` of quotients $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$, where for some weight $k$ the forms $f, g$ are modular forms of weight $k$ on $\Gamma$ (regarded inside $\mathrm{GL}_2(\mathbb{R})$), $p_f, p_g \in \mathbb{Z}[[q]]$ are integral $q$-expansions of $f$ and $g$ in the sense of `IsIntegralQExp`, and the reduction $\mathrm{intSeriesC}\,K\,p_g$ is nonzero. Let $\mathrm{Frob} =$ `qExpFrobeniusModL K Γ ℓ` be the $K$-algebra endomorphism of $\bar F$ induced by the substitution $q \mapsto q^{\ell}$ on Laurent series (multiplication by $\ell$ on exponents). Assume that $\bar F$ is a function field of one variable over $K$ in the sense that there is an $x \in \bar F$ transcendental over $K$ with $\bar F$ finite-dimensional over $K(x) = \mathrm{adjoin}\,K\,\{x\}$. The conclusion is twofold. First, `QExpFrobeniusInputsModL K Γ ℓ` holds: there is a `HasPrincipalDivisors K` $\bar F$ structure, that is, every nonzero $f \in \bar F$ admits a divisor $D$ of degree $0$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ of $\bar F/K$; and there is a witness that $\bar F$ is a finite module over itself for the algebra structure along $\mathrm{Frob}$, for which both the property `FundamentalIdentity` of the extension $\bar F/\mathrm{Frob}$ (with the integrality of $\mathrm{Frob}$ as input) and the divisor push-forward norm property `Divisor.PushforwardNormFormula` along $\mathrm{Frob}$ hold. Second, the rank of $\bar F$ as a module over itself along $\mathrm{Frob}$, [`AlgebraicCurve.finrankAlong K (qExpFrobeniusModL K Γ ℓ)`](def/AlgebraicCurve_Correspondence.html#L51), equals $\ell$.
--
--   This packages the hypotheses under which the mod-$\ell$ Frobenius substitution $q \mapsto q^{\ell}$ on the $q$-expansion function field of $X(\Gamma)$ induces push-forward and pull-back maps on degree-zero divisor classes, together with the computation $[\bar F : \mathrm{Frob}(\bar F)] = \ell$ reflecting that $\mathrm{Frob}(\bar F)$ is the field of $\ell$-th powers. It feeds the analysis of Frobenius on the reduction of modular curves, in particular the statements on places and ordinals of Frobenius twists and on norms of torsion points cited downstream; the proof invokes [`AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField`](thm.html#AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField) and [`AlgebraicCurve.exists_separating_transcendental_of_perfectField`](thm.html#AlgebraicCurve.exists_separating_transcendental_of_perfectField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.QExpFrobeniusInputsModL K Γ ℓ ∧
      AlgebraicCurve.finrankAlong K (ModularCurve.qExpFrobeniusModL K Γ ℓ) = ℓ := by sorry
