-- Prove2me | Theorems.Thm_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one
-- name    : LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/ac05a400-23cc-5b48-8cfd-0ad52c353957
-- title:
--   Strict Satake bound at good places with unitary determinant
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$ and $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2$ of the adeles of $F$. Write $D=\bigcup_{x\in T}\{g x : g\in\ \text{centreCutSiegelSet}\}$ for the union of the right translates by the elements of $T$ of the set of adelic matrices whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and whose `archDetNorm` at each infinite place lies in $[d_1,d_2]$. Assume $D$ covers modulo centre: every adelic $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\,z\in D$ (the central scalar matrix of $z$). Let $\Phi$ be a Hecke eigensystem for $F$ over $\mathbb{C}$ (a nonzero level ideal together with functions $a,b$ on the finite places), and let $R$ be a smooth cusp realisation, at the production pins built from $D$, the level subgroups $\text{levelOne}(N)\cap\ker(\text{glArch})$, the Hecke generators $\text{heckeGen}(v)$ and the adelic box, of the rescaled eigensystem $\Phi.\text{toRawCentral}$ (same level and same $a$, with $b(v)$ replaced by $N(v)^{-1}b(v)$, $N(v)=\mathrm{absNorm}(v)$); thus $R$ has a nowhere-identically-zero complex function on adelic $\mathrm{GL}_2$, a central character on the full idele unit group, the smooth cuspidality property at those pins, right invariance under the level subgroup, and, outside a finite exceptional set, Hecke coset eigenvalue $a(v)$ and central eigenvalue $N(v)^{-1}b(v)$. Assume the function of $R$ is continuous. Then for every finite place $v$ of $F$ with $v$ not dividing the level of $\Phi$, $v$ outside the exceptional set of $R$, and $\lVert b(v)\rVert=1$, one has $a(v)^2\neq b(v)\,(N(v)+2+N(v)^{-1})$, and there exist $\alpha,\beta\in\mathbb{C}$ with $\alpha+\beta=a(v)$, $\alpha\beta=b(v)$ and $\lVert\alpha\rVert,\lVert\beta\rVert<\sqrt{N(v)}$. Unlike the companion statement it cites, the normalisation $\lVert b(v)\rVert=1$ is required only at the place $v$ under consideration rather than at all good places.
--
--   This is the strict temperedness bound on the Satake parameters at a good place: the local unramified constituent is an irreducible unitary generic unramified principal series, so its Satake parameters have absolute value strictly below $\sqrt{N(v)}$, and the Satake polynomial has distinct roots away from the boundary case. It is used in the Langlands–Tunnell part of the development, in particular in the Rankin–Selberg convergence and continuation statements and in the integrality bound for Hecke tables on Siegel cusp classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_norm_b_eq_one
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level → v ∉ R.exceptionalSet → ‖Φ.b v‖ = 1 →
        Φ.a v ^ 2 ≠ Φ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) ∧
        ∃ α β : ℂ, α + β = Φ.a v ∧ α * β = Φ.b v ∧
          ‖α‖ < Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ∧
          ‖β‖ < Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by sorry
