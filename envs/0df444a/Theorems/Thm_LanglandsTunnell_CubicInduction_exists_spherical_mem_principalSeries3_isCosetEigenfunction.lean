-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries3_isCosetEigenfunction
-- name    : LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries3_isCosetEigenfunction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/055427fb-ce6e-598d-b40a-90d970bddd60
-- title:
--   Spherical vector in an unramified principal series of GL₃
-- statement:
--   Let $v$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$, and let $\chi = (\chi_0,\chi_1,\chi_2)$ be a triple of group homomorphisms $\mathbb{Q}_v^\times \to \mathbb{C}^\times$, each of which is assumed trivial on every unit of norm $1$. Write $\varpi$ for `uniformizerUnit` at $v$, $\alpha_i := \chi_i(\varpi)$, $N(v)$ for the absolute norm of the ideal $v$ (the constant `cNormQ v`), and $U :=$ `localMaximalCompact3`, the subgroup of $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries and all of whose entries of $g^{-1}$ have valuation $\le 1$. Then there is an element $f$ of the space `principalSeries3 v χ` — that is, a locally constant $f : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ with $f(n g) = f(g)$ for all upper unipotent $n =$ `upperUnipotent3 x y z` and $f(\mathrm{diag}(a)g) = \bigl(\prod_i \chi_i(a_i)\bigr)\,(\|a_0\|/\|a_2\|)\, f(g)$ for $a \in (\mathbb{Q}_v^\times)^3$ — such that: $f(1) = 1$; $f(gu) = f(g)$ for all $u \in U$; for $\mathrm{gen} = \mathrm{diag}(\varpi,1,1)$ and for $\mathrm{gen} = \mathrm{diag}(\varpi,\varpi,1)$, and for every finite family of representatives `reps` forming a Hecke coset system for $(U,\mathrm{gen})$, one has $\sum_i f(g\cdot \mathrm{reps}_i) = \lambda f(g)$ for all $g$, with $\lambda = N(v)(\alpha_0+\alpha_1+\alpha_2)$ in the first case and $\lambda = N(v)(\alpha_0\alpha_1+\alpha_0\alpha_2+\alpha_1\alpha_2)$ in the second; and $f(\mathrm{diag}(\varpi,\varpi,\varpi)\,g) = \alpha_0\alpha_1\alpha_2\, f(g)$ for all $g$.
--
--   This is the existence of the spherical (Satake) vector in the normalised unramified principal series of $\mathrm{GL}_3$ over the completion at $v$, together with the Satake eigenvalues of the two degree-one and degree-two spherical Hecke coset operators and the action of the centre. It feeds the local unramified input of the cubic induction, being used by `exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one` to recognise a Hecke eigenfunction with the given eigenvalues as a coefficient function of a principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries3_isCosetEigenfunction.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries3_isCosetEigenfunction
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1) :
    ∃ f : ↥(principalSeries3 v χ), (f : LocalGL3 v → ℂ) 1 = 1 ∧
      IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (f : LocalGL3 v → ℂ) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) (f : LocalGL3 v → ℂ)
        (cNormQ v * (((χ 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) + ((χ 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) + ((χ 2 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ))) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) (f : LocalGL3 v → ℂ)
        (cNormQ v * (((χ 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) + ((χ 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 2 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) + ((χ 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 2 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ))) ∧
      ∀ g : LocalGL3 v, (f : LocalGL3 v → ℂ) (centralGen v * g) =
        ((χ 0 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 1 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * ((χ 2 (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ) * (f : LocalGL3 v → ℂ) g := by sorry
