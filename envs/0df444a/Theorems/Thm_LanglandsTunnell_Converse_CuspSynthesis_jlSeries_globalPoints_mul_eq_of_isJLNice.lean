-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_CuspSynthesis_jlSeries_globalPoints_mul_eq_of_isJLNice
-- name    : LanglandsTunnell.Converse.CuspSynthesis.jlSeries_globalPoints_mul_eq_of_isJLNice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/6d60d521-86dc-549f-a329-f5a3e07c5bbb
-- title:
--   Invariance of the Jacquet–Langlands Whittaker series under GL₂(K)
-- statement:
--   Let $K$ be a number field, $\Pi$ a Hecke eigensystem over $\mathbb{C}$ for $K$ (a nonzero level ideal together with families $a_v, b_v \in \mathbb{C}$ indexed by the finite places), and $S$ a finite set of finite places. Fix archimedean parameters $\mathrm{archR}$ at the real places (principal, given by two exponents in $\mathbb{C}$ and two signs in $\mathbb{Z}/2$, or discrete, given by an exponent and a weight $k \ge 1$) and $\mathrm{archC}$ at the complex places (exponents $u_1,u_2$ and integers $k_1,k_2$); characters $\mathrm{epsS}_v$ of the local unit groups $(K_v)^\times$ for all finite $v$; and an idele class character $\omega$ which is trivial on principal ideles, continuous and unitary, is trivial on the units of $\mathcal{O}_v$ for $v \notin S$, satisfies $\omega(\varpi_v) = b_v$ for the eigensystem obtained from $\Pi$ by twisting by $v \mapsto N(v)^{-1/2}$ at all $v \notin S$, and whose component at each infinite place is the quasi-character with exponent the central exponent of the parameter there and with the central sign (real case) or central twist (complex case). Let $d$ be Jacquet–Langlands data of type $(S,\mathrm{epsS},\omega)$: exponents $m_v \ge 1$ for $v \in S$ with $\mathrm{epsS}_v$ and the local component of $\omega$ trivial on units congruent to $1$ modulo $\mathfrak{p}_v^{m_v}$, an element $A \in K^\times$ of valuation $\exp(-m_v)$ at each $v \in S$, and bounded coefficient functions $a, a^\vee : K^\times \to \mathbb{C}$ with $a$ not identically zero, transforming by the prescribed local characters under multiplication by $S$-units and vanishing outside the conductor bound given by the level of the local additive characters. Let $dR$, $dC$ be archimedean Whittaker data for the parameters at the real and complex places (functions on $\mathrm{GL}_2(\mathbb{R})$, resp. $\mathrm{GL}_2(\mathbb{C})$, smooth, with the unipotent and central transformation laws, whose zeta integrals are entire after removal of the archimedean factor, of finite order, bounded on strips, satisfying the local functional equation with the $\epsilon$-factor, and with the stated decay), and let $dF$ be a finite Whittaker datum for $(S,\Pi)$: a function on $\mathrm{GL}_2(\mathbb{A})$ depending only on the finite component, invariant under $\mathrm{GL}_2(K_v)$ on the right for $v \in S$, transforming by the standard additive character under left unipotents and invariant under $\mathrm{GL}_2(\mathcal{O}_v)$ on the right for $v \notin S$, a Hecke eigenfunction with eigenvalues $\Pi.a_v$ and central eigenvalues given by $\Pi$'s raw central datum outside $S$, and right invariant under some nonzero level. Assume $\mathrm{IsJLNice}$ holds for $K$, $S$, $\mathrm{epsS}$, $\omega$, $d$, the twist of $\Pi$ by $v \mapsto N(v)^{-1/2}$ and the archimedean parameters: there is a system of representatives of $S$-valuation vectors in $K^\times$ such that, for every admissible twist $\mu$ whose local components cancel the $\mathrm{epsS}_v$ on the units at places of $S$ and every archimedean exponent data compatible with $\mu$, the twisted $L$-datum is well formed and convergent and there are entire functions $\Lambda, \Lambda^\vee$, bounded on vertical strips, which in a right half-plane equal the $S$-sums times the archimedean factors and the $L$-functions of that datum, and which satisfy the functional equation $\Lambda(s) = \mathrm{sFactor}(s)\,\varepsilon\, C^{1/2-s}\Lambda^\vee(1-s)$ with the pinned root number and the finite conductor. Then for every $\gamma \in \mathrm{GL}_2(K)$ and every $g \in \mathrm{GL}_2(\mathbb{A})$ such that both $g$ and $\gamma g$ (with $\gamma$ mapped to the adeles) satisfy, at every $v \in S$, the conditions that the valuation of the $(1,1)$ entry is nonzero, equals that of the $(0,0)$ entry, dominates that of the $(0,1)$ entry, and dominates $\exp(m_v)$ times that of the $(1,0)$ entry, the Whittaker-type series $\sum'_{\alpha \in K^\times} a(\alpha)\,\mathrm{epsChar}(h)\,W_\infty(\mathrm{diag}(\alpha,1)h)\,W_f(\mathrm{diag}(\alpha,1)h)$, with $W_\infty$ the archimedean Whittaker function times the archimedean norm factor, takes the same value at $h = \gamma g$ and at $h = g$.
--
--   This is the left $\mathrm{GL}_2(K)$-invariance step in the converse theorem of Weil and Jacquet–Langlands: the series synthesised from Jacquet–Langlands data is shown to descend, on the prescribed level set at the places of $S$, to a function on $\mathrm{GL}_2(K)\backslash \mathrm{GL}_2(\mathbb{A})$. It feeds the construction of an arithmetic genuine cuspidal realisation of the given Hecke eigensystem from the analytic hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_CuspSynthesis_jlSeries_globalPoints_mul_eq_of_isJLNice.lean

import Definitions.Def_LanglandsTunnell_JLSynthesis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.TateGlobal
open LanglandsTunnell.Converse LanglandsTunnell.Converse.CuspSynthesis in

theorem LanglandsTunnell.Converse.CuspSynthesis.jlSeries_globalPoints_mul_eq_of_isJLNice
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ω v)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archR w hw).centralExponent ((archR w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC) :
    ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
      globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
      jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g := by sorry
