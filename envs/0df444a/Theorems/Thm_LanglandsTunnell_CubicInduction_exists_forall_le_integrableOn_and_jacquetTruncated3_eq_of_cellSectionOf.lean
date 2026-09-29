-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
-- name    : LanglandsTunnell.CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/484d2187-2f82-5928-94cd-1cf228f0d8a6
-- title:
--   Stabilisation of truncated Jacquet integrals of translated cell sections
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_v$ carried by its Borel $\sigma$-algebra `localBorel`. Let $\nu_0,\nu_1,\nu_2 : \mathbb{Q}_v^{\times} \to \mathbb{C}^{\times}$ be multiplicative characters, each locally constant, let $\Phi : \mathbb{Q}_v^{3} \to \mathbb{C}$ be locally constant with compact support, and let $g \in \mathrm{GL}_3(\mathbb{Q}_v)$. Write $W$ for the right translate $h \mapsto (\mathrm{cellSectionOf}\ v\ \nu\ \Phi)(hg)$ of the cell section, i.e. of the function supported on $\{h : \mathrm{cornerEntry}\ h \neq 0,\ \mathrm{lowerMinor}\ h \neq 0\}$ given there by $\mathrm{charExt}(\nu_0)(\det h/\mathrm{lowerMinor}\ h)\,\mathrm{charExt}(\nu_1)(\mathrm{lowerMinor}\ h/\mathrm{cornerEntry}\ h)\,\mathrm{charExt}(\nu_2)(\mathrm{cornerEntry}\ h)\cdot(\|\det h/\mathrm{lowerMinor}\ h\|/\|\mathrm{cornerEntry}\ h\|)$ times $\Phi$ evaluated at $\mathrm{cellRatio}\ h = (h_{21}/\mathrm{cornerEntry}\ h,\ h_{22}/\mathrm{cornerEntry}\ h,\ \mathrm{outerMinor}\ h/\mathrm{lowerMinor}\ h)$. The assertion is the existence of $c_0 \in \mathbb{N}$ such that for every integer $c \geq c_0$: first, the function $(x,y,z) \mapsto \psi_v(-(x+y))\,W(w\cdot u(x,y,z))$, with $\psi_v$ the local component at $v$ of the standard adelic additive character, $w$ the antidiagonal permutation matrix of `antidiagonal3` and $u(x,y,z)$ the upper unipotent matrix with entries $x,y,z$, is integrable on the ball $\{\,|x| \leq \exp c,\ |y| \leq \exp c,\ |z| \leq \exp(2c)\,\}$ against the triple product of the self-dual Haar measure `selfDualHaarAt`; and second, $\mathrm{jacquetTruncated3}\ v\ c\ W = \mathrm{jacquetTruncated3}\ v\ c_0\ W$, i.e. the integral of that same integrand over the ball of level $c$ agrees with the one at level $c_0$.
--
--   This is the stabilisation statement for the local Jacquet (Whittaker) integrals attached to a translated section of a principal series on $\mathrm{GL}_3$ at a finite place: beyond one explicit truncation level the integrals no longer depend on the level, so the Whittaker functional is well defined by truncation. It is used by the computations of the dual and torus Jacquet value functions, in particular in showing that the threefold twisted differences of those functions eventually vanish; the proof invokes the smoothness of sections of the principal series together with the level-zero normalisation and nontriviality of the local additive character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 v) :
    letI := localBorel ℚ v
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      IntegrableOn (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => psiLocal ℚ v (-(p.1 +
        p.2.1)) * (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) (antidiagonal3 v * upperUnipotent3 p.1
        p.2.1 p.2.2)) (unipotentBall3 v c) (jacquetHaar3 v) ∧
      jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) = jacquetTruncated3 v c₀
        (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf v ν Φ)) := by sorry
