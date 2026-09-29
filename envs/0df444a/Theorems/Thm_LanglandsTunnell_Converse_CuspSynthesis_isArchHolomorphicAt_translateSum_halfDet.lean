-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet
-- name    : LanglandsTunnell.Converse.CuspSynthesis.isArchHolomorphicAt_translateSum_halfDet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/47ab2f35-f18d-58f1-a519-f1cd78ca669b
-- title:
--   Holomorphy at real places of half-determinant twisted translate sums
-- statement:
--   Let $K$ be a number field, $\Pi$ a Hecke eigensystem over $K$ with complex coefficients (a nonzero level ideal together with families $a_v$, $b_v$ indexed by the finite places), $S$ a finite set of finite places, and let $\mathrm{archR}$, $\mathrm{archC}$ assign to each real place a real archimedean parameter (principal or discrete) and to each complex place a parameter $(u_1,k_1,u_2,k_2)$. Let $\epsilon_S$ assign to each finite place $v$ a character $(K_v)^\times \to \mathbb{C}^\times$, and let $\omega$ be a character of the idele units which is trivial on $K^\times$, continuous and unitary, and which satisfies $\omega(\varpi_v) = N(v)^{-1} b_v$ for every $v \notin S$, i.e. $\omega$ at the uniformiser idele equals the $b$-coefficient of the twist of $\Pi$ by $v \mapsto N(v)^{-1/2}$. Let $d$ be a `JLData` for $S$, $\epsilon_S$, $\omega$ (levels $m_v \ge 1$ at the places of $S$ with $\epsilon_S$ and the local component of $\omega$ trivial on units congruent to $1$ modulo $m_v$, an element $A \in K^\times$ of prescribed valuations, and bounded coefficient functions $a$, $a^{\vee}$ on $K^\times$ with the $S$-unit transformation laws, the vanishing condition outside the conductor range, and $a \neq 0$), let $d_R$, $d_C$ be archimedean Whittaker data for the parameters at the real and complex places (Whittaker function with unipotent and central transformation laws, smoothness, entire zeta integrals with functional equation, finite order and decay), and let $d_F$ be a finite Whittaker datum for $S$ and $\Pi$ (a function of the finite part only, invariant under the $S$-components, $\psi$-equivariant under unipotents and right invariant under integral matrices outside $S$, a Hecke eigenfunction with eigenvalues $a_v$ and central eigenvalues $(c_v)^{-1}b_v$ outside $S$, and right invariant under some level subgroup). Assume `IsJLNice` holds for these data and the twist of $\Pi$ by $v \mapsto N(v)^{-1/2}$: there are $S$-order representatives such that for every admissible twist $\mu$ with prescribed archimedean components the associated $L$-datum is well formed and convergent, and the two completed series are entire, bounded on vertical strips and related by the expected functional equation with root number and conductor. Assume further that at each real place $w$ and for each $x \in \mathrm{GL}_2(\mathbb{R})$ the function $z \mapsto (\operatorname{Im} z)^{-1} W_w(x \cdot \mathrm{iwasawaSectionGL}\,z)$ is holomorphic on the upper half-plane, where $W_w$ is the Whittaker function of $d_R$ at $w$. Finally let $k_1,\dots,k_n$ be elements of the adelic $\mathrm{GL}_2$ with trivial archimedean component, $c_1,\dots,c_n \in \mathbb{C}$, and assume the Whittaker series $\mathrm{jlSeries}'$ of the data is left invariant by $\mathrm{GL}_2(K)$ in the weak sense that $\mathrm{jlSeries}'(\gamma g) = \mathrm{jlSeries}'(g)$ whenever $g$ and $\gamma g$ both lie in the set $\mathrm{kZeroSet}\,S\,d.m$ cut out by the valuation inequalities on the matrix entries at the places of $S$. Then for every real place $w$ the function $g \mapsto \bigl(\sum_i c_i\,\mathrm{theForm}(g k_i)\bigr)\cdot \|\det g\|^{1/2}$, where $\mathrm{theForm}$ denotes the function on the adelic group attached to $d$, $\mathrm{archR}$, $\mathrm{archC}$, $d_R$, $d_C$, $d_F$ and $\|\cdot\|$ is the idele norm, satisfies `IsArchHolomorphicAt w`: for every adelic $g$, the function $z \mapsto (\operatorname{Im} z)^{-1}$ times its value at $g$ times the image of $\mathrm{iwasawaSectionGL}\,z$ under the embedding of $\mathrm{GL}_2$ at $w$ is differentiable on the upper half-plane as a map of complex manifolds.
--
--   This is the holomorphy input, at the real places, for the Weil-type converse construction on $\mathrm{GL}_2$ over a number field: the half-determinant twist of a finite combination of right translates by finite-adelic elements inherits holomorphy from the archimedean Whittaker data. It is used in the assembly of an arithmetic genuine cusp realisation from nice twisted data, [`LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_of_isJLNice`](thm.html#LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_of_isJLNice), and relies on the growth and local majorant estimates for nice data together with the factorisation of the idele norm of the determinant into archimedean contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_CuspSynthesis_isArchHolomorphicAt_translateSum_halfDet.lean

import Definitions.Def_LanglandsTunnell_JLSynthesis
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_JLData
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.TateGlobal
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.CuspSynthesis.isArchHolomorphicAt_translateSum_halfDet
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (hhol : ∀ (w : InfinitePlace K) (hw : w.IsReal) (x : GL (Fin 2) ℝ),
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
          ((z.im : ℝ) : ℂ)⁻¹ *
            (dR w hw).W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    {n : ℕ} (ks : Fin n → AdelicGL2 (𝓞 K) K) (hks : ∀ i, ks i ∈ finiteAdelicGL2Subgroup K)
    (cs : Fin n → ℂ)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (w : InfinitePlace K) (hw : w.IsReal) :
    IsArchHolomorphicAt w hw fun g =>
      translateSum d archR archC dR dC dF ks cs g *
        (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by sorry
