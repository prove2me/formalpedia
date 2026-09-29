-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_CubicInductionData_dualWhittaker_eq_dualWhittakerFn3
-- name    : LanglandsTunnell.CubicInduction.CubicInductionData.dualWhittaker_eq_dualWhittakerFn3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/62307a15-f98b-5189-95aa-bc82b1f0506a
-- title:
--   Dual Whittaker function as the reflected Whittaker function
-- statement:
--   Fix an additive character $\psi$ of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, a subset $D$ of the adelic $\mathrm{GL}_2$, a family $U$ of subgroups of the adelic $\mathrm{GL}_2$ indexed by the ideals of $\mathbb{Z}$, a family $\mathrm{gen}$ of elements of the adelic $\mathrm{GL}_2$ indexed by the height one spectrum, and a term $X$ of `CubicInductionData`, whose fields include functions `form`, `whittaker`, `dualWhittaker` on $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$. Assume: (i) `X.form` is invariant under left translation by the image of $\mathrm{GL}_3(\mathbb{Q})$ in the adelic group; (ii) for every $g$, `X.whittaker` $g$ is the iterated integral $\int\!\int\!\int X.\mathrm{form}(u(x,y,z)g)\,\psi(-(x+y))$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$ and each integration is against the additive Haar measure of the adeles conditioned on the adelic box (infinite part in the fundamental domain of the lattice basis, finite part integral at every place), the measure being the one carried by the pins `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`; (iii) `X.whittaker`$(u(x,y,z)g) = \psi(x+y)\,$`X.whittaker`$(g)$ for all adeles $x,y,z$ and all $g$; (iv) for every $g$ the family $i \mapsto$ `X.whittaker`$(\gamma_i g)$, indexed by the quotient of $\mathrm{GL}_2(\mathbb{Q})$ by the right relation attached to the range of the unipotent embedding and with $\gamma_i$ the image in adelic $\mathrm{GL}_3$ of a chosen representative, is summable with sum `X.form`$(g)$; (v) for every $g$, `X.dualWhittaker`$(g)$ is the same iterated integral taken with $\psi^{-1}$ in place of $\psi$ and with $g \mapsto X.\mathrm{form}({}^{t}g^{-1})$ in place of `X.form`; and (vi) `X.form` is continuous. Then `X.dualWhittaker` equals the function $g \mapsto$ `X.whittaker`$(w_3\,{}^{t}g^{-1})$, where $w_3$ is the antidiagonal permutation matrix in $\mathrm{GL}_3$.
--
--   This identifies the dual Whittaker field of the data with the contragredient Whittaker function $\widetilde{W}(g) = W(w_3\,{}^{t}g^{-1})$ of Jacquet, Piatetski-Shapiro and Shalika, the form in which the functional equation of $\mathrm{GL}_3$ Rankin–Selberg integrals is phrased. It is used in the construction of cubic induction data and in the statement that the associated global zeta integral continues to an entire function matching the dual zeta integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_CubicInductionData_dualWhittaker_eq_dualWhittakerFn3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.CubicInductionData.dualWhittaker_eq_dualWhittakerFn3
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) (X : CubicInductionData)
    (hauto : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      X.form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = X.form g)
    (hW : ∀ g, X.whittaker g =
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ X.form g)
    (hWlaw : IsGL3PsiWhittakerFn ψ X.whittaker)
    (hexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ => X.whittaker (mirabolicTranslate i * g)) (X.form g))
    (hWd : ∀ g, X.dualWhittaker g =
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ (dualForm X.form) g)
    (_hcont : Continuous X.form) :
    X.dualWhittaker = dualWhittakerFn3 X.whittaker := by sorry
