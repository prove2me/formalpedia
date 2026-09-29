-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/49843cb3-f3e4-56ff-a08c-18405ee4b78b
-- title:
--   Factorisation of the dual Whittaker function over a finite set of places
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let `pins` be a package of carrier data for $\mathbb{Q}$ (a measurable space and measure on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, a fundamental domain, a central subgroup, level subgroups, local generators, and a measurable space and measure on $\mathbb{A}_{\mathbb{Q}}$), let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ with values in $\mathbb{C}$, and let $\mu$ be a character of the ideles of $K$. Let $X$ be a `CubicInductionData`, that is, a tuple consisting of a function `form` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, a global Whittaker function `whittaker`, local Whittaker functions `whittakerLoc v` for the finite places $v$ of $\mathbb{Q}$, an archimedean Whittaker function `whittakerArch`, a central character, and a function `dualWhittaker`. Assume `IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X`, the conjunction of the defining clauses for such data relative to the set of places $v$ that are bad for $(K,\mu)$, i.e. satisfy `IsRamifiedIn K v` or `IsTwistRamifiedAbove K μ v` (automorphy and central-character behaviour of `form`, cuspidality along the two maximal parabolics, the integral formula and $\psi$-Whittaker law for `whittaker` together with its mirabolic expansion summing to `form`, the Whittaker law, sphericity outside the bad set, level invariance, multiplicity one for the `whittakerLoc v`, factorisability of `whittaker` into its archimedean and local components over any finite set of places containing the bad ones, moderate growth, $K$-finiteness, the moment and half-plane conditions, and the corresponding clauses for `dualWhittaker` and the dual form; summarised here). Assume further that `X.dualWhittaker` equals `dualWhittakerFn3 X.whittaker`, namely $g \mapsto$ `X.whittaker` $(w_3 \cdot {}^{t}g^{-1})$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$. Then for every $g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ and every finite set $T$ of finite places of $\mathbb{Q}$ containing all bad places, such that for $v \notin T$ the component $g_v$ lies in `localMaximalCompact3`, the subgroup of matrices in $\mathrm{GL}_3$ over the completion at $v$ all of whose entries and whose inverse's entries have valuation at most $1$, one has $$X.\mathrm{dualWhittaker}(g) = \widetilde{W}_{\infty}(g_\infty) \prod_{v \in T} \widetilde{W}_{v}(g_v),$$ where $\widetilde{W}_\infty$ and $\widetilde{W}_v$ denote `dualWhittakerFn3` applied to `X.whittakerArch` and to `X.whittakerLoc v` respectively.
--
--   This transports the Euler factorisation of the global Whittaker function of cubic induction data across the involution $W \mapsto (g \mapsto W(w_3\,{}^{t}g^{-1}))$, so that the dual Whittaker function admits the same decomposition into an archimedean factor and finitely many local factors. It is the input needed to factor the global zeta integral attached to the dual side, and is used in the functional-equation statements for the $\mathrm{GL}_3 \times \mathrm{GL}_1$ global zeta integral and in their specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (hD1 : X.dualWhittaker = dualWhittakerFn3 X.whittaker)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v, IsBadPlace K μ v → v ∈ T)
    (hg : ∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    X.dualWhittaker g =
      dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
        ∏ v ∈ T, dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v g) := by sorry
