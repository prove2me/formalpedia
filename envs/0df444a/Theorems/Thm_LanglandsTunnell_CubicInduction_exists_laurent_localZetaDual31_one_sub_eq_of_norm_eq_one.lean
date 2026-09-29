-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZetaDual31_one_sub_eq_of_norm_eq_one
-- name    : LanglandsTunnell.CubicInduction.exists_laurent_localZetaDual31_one_sub_eq_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/5ae1fa23-b85a-58ef-b913-891fcd7e49b8
-- title:
--   Laurent form of the dual local zeta integral at v
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), with completion $\mathbb{Q}_v$ and residue cardinality $q_v=\mathrm{absNorm}(v)$. Let $\nu_0,\nu_1,\nu_2$ be homomorphisms $\mathbb{Q}_v^{\times}\to\mathbb{C}^{\times}$, each locally constant, let $\Phi:\mathbb{Q}_v^{3}\to\mathbb{C}$ be locally constant with compact support, and let $\chi:\mathbb{Q}_v^{\times}\to\mathbb{C}^{\times}$ be a locally constant homomorphism, subject to $\|(\nu_i\chi)(\varpi_v)\|=1$ for each $i$, where $\varpi_v$ is the unit `uniformizerUnit`. Equip $\mathbb{Q}_v$ with its Borel structure. The assertion is the existence of a function $P^{\vee}:\mathbb{C}\to\mathbb{C}$ of Laurent type, namely $P^{\vee}(s)=Q(q_v^{-s})\,q_v^{m s}$ for some $Q\in\mathbb{C}[X]$ and some $m\in\mathbb{N}$, such that for every $s$ with $\operatorname{Re}(1-s)>0$ one has $$\mathrm{localZetaDual31}\bigl(\mu,\;\sigma_v,\;h\mapsto \mathrm{jacquetWhittaker3}\,(\nu,\Phi)(h\cdot w_0),\;\chi,\;1-s\bigr)(1)=\Bigl(\prod_{i}\mathrm{localLFactorAt}\,(\nu_i\chi)^{-1}(1-s)\Bigr)\cdot P^{\vee}(s).$$ Here $\sigma_v$ is the self-dual additive Haar measure `selfDualHaarAt` (the Haar measure of the integers scaled by $q_v^{-n_v/2}$, $n_v$ the level of the standard additive character), $\mu$ is the pullback along `Units.val` of $\sigma_v$ restricted off $0$ with density $|x|^{-1}$, and $w_0=\mathrm{antidiagonal3}$. Unfolding, `localZetaDual31` is the double integral $\int_{\mathbb{Q}_v^{\times}}\bigl(\int_{\mathbb{Q}_v} W^{\vee}(\iota(\mathrm{diag}(a))\,n^{-}(x)\,g_0)\,d\sigma_v(x)\bigr)\chi^{-1}(a)\,|a|^{-s}\,d\mu(a)$, taken at $g_0=\mathrm{weylPrime3}\cdot\mathrm{transposeInv3}(1)$, with $W^{\vee}(g)=W(\mathrm{longWeyl3}\cdot \mathrm{transposeInv3}(g))$ and $W$ the function above; `jacquetWhittaker3` is the truncated unipotent value `jacquetValue` of the right translate of the big-cell section `cellSectionOf`, which is supported on $\mathrm{bigCell3}$ where it equals $\mathrm{cellValue}(\nu,g)\,\Phi(\mathrm{cellRatio}\,g)$; and $\mathrm{localLFactorAt}\,\lambda(w)$ is $(1-\lambda(\varpi_v)q_v^{-w})^{-1}$ when $\lambda$ has conductor exponent $0$ and $1$ otherwise.
--
--   This is the dual half of the local theory of the $GL_3\times GL_1$ zeta integrals attached to a big-cell Whittaker section: the integral at $1-s$ is the product of the local $L$-factors of the inverse twists $(\nu_i\chi)^{-1}$ with a Laurent polynomial in $q_v^{-s}$. It is used, together with the corresponding statement for the zeta integral at $s$, to produce the local functional equation `exists_laurent_localZeta_fe_of_jacquetWhittaker3_mul_antidiagonal3`, which feeds the converse-theorem input of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_laurent_localZetaDual31_one_sub_eq_of_norm_eq_one.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_laurent_localZetaDual31_one_sub_eq_of_norm_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) :
    letI := localBorel ℚ v
    ∃ Pd : ℂ → ℂ,
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        Pd s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      ∀ s : ℂ, 0 < (1 - s).re →
        localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
            (fun h => jacquetWhittaker3 v ν Φ (h * antidiagonal3 v)) χ (1 - s) 1 =
          (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) * Pd s := by sorry
