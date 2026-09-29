-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_of_isJLNice
-- name    : LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_of_isJLNice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/85161de1-77f0-59df-9ee3-21dddf72401c
-- title:
--   Converse theorem for GL₂: nice L-data give cuspidal realisations
-- statement:
--   Throughout, $K$ is a number field; $c,u,d_1,d_2$ are real numbers with $0<c$ and $0<d_1$; and $T$ is a finite subset of $\mathrm{GL}_2$ of the adeles of $K$ (`AdelicGL2 (𝓞 K) K`).
--
--   **The eigensystem and the local data.** $\Pi$ (`Pi`) is a Hecke eigensystem over $K$ with complex values: a nonzero ideal $\Pi.\mathrm{level}$ of $\mathcal O_K$ together with families $a_v,b_v\in\mathbb C$ indexed by the finite places of $K$. Write $\Pi^{u}$ for the twist `Pi.twist (fun v => (Ideal.absNorm v.asIdeal)^(-1/2))`, which has the same level, $a$-values $(Nv)^{-1/2}a_v$ and $b$-values $(Nv)^{-1}b_v$. Further data: a finite set $S$ of finite places; for each real place $w$ a parameter $P_w=$ `archR w hw` of type `RealArchParam` (a principal pair $(u_1,a_1,u_2,a_2)$ with $a_i\in\mathbb Z/2$, or a discrete parameter $(u,k)$ with $k\ge 1$); for each complex place $w$ a parameter $Q_w=$ `archC w hw` of type `ComplexArchParam` (data $u_1,k_1,u_2,k_2$); for every finite place $v$ a character $\varepsilon_v$ of $(K_v)^\times$ with values in $\mathbb C^\times$ (`epsS`); and a character $\omega$ of the idele group of $K$ with values in $\mathbb C^\times$.
--
--   **Hypotheses on $\omega$.** `hω` is `IsAdmissibleTwist`: $\omega$ is trivial on the principal ideles coming from $K^\times$, continuous, and unitary. `hωunr` requires $\omega$ to be unramified at every $v\notin S$, in the sense of `IsUnramifiedCharAt`: its local component is trivial on those $t\in (K_v)^\times$ with $t$ and $t^{-1}$ both integral. `hωb` requires, for every $v\notin S$, that $\omega$ evaluated at the uniformizer idele at $v$ equals the $b$-value of $\Pi^{u}$ at $v$, i.e. $(Nv)^{-1}b_v$. `hωR` requires, at each real place $w$, that `IsArchCompAt K ω w` holds with exponent the central exponent of $P_w$ and integer parameter the representative in $\mathbb Z$ of the central sign of $P_w$; that is, the local component of $\omega$ at $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\cdot u}\,(x/\|x\|)^{a}$ for those $u,a$. `hωC` requires the same at each complex place, with exponent the central exponent of $Q_w$ and integer parameter its central twist $k_1+k_2$.
--
--   **The $S$-data.** $d$ is a `JLData K S epsS ω`: exponents $m_v\ge 1$ for $v\in S$; triviality of $\varepsilon_v$ and of the local component of $\omega$ on local units of valuation $1$ satisfying `IsOneMod K v (m v)`; an element $A\in K^\times$ whose local valuation at each $v\in S$ is $\exp(-m_v)$; uniformly bounded functions $a,\tilde a\colon K^\times\to\mathbb C$ which, upon multiplication of the argument by an $S$-unit $\beta$, are multiplied by $\prod_{v\in S}\varepsilon_v(\beta_v)$ respectively by $\prod_{v\in S}\omega_v(\beta_v)\varepsilon_v(\beta_v)^{-1}$; the vanishing of both $a$ and $\tilde a$ at any $\alpha$ whose local valuation at some $v\in S$ fails to be at most $\exp$ of the level of the local additive character `psiLocal`; and $a\not\equiv 0$.
--
--   **The Whittaker data.** For each real place $w$, `dR w hw` is an `ArchDatumR (archR w hw)`: a function $W$ on real $2\times 2$ matrices, smooth on the invertible locus, with $W(n(x)g)=\psi(x)W(g)$ and the central law $W(zg)=\chi_{P_w}(z)\,|z|\,W(g)$ for $z\neq 0$, together with entire functions `zetaEntire` of a complex variable depending on a twist $(u,a)\in\mathbb C\times\mathbb Z/2$, an abscissa beyond which the zeta integrand is integrable and its integral equals the archimedean factor of the twisted parameter times `zetaEntire`, a functional equation relating `zetaEntire` at $(w_0g,-(u+\text{central exponent}),a+\text{central sign},1-s)$ to the epsilon factor of the twisted parameter times `zetaEntire` at $(g,u,a,s)$, finite order in vertical strips, and decay estimates on all derivatives for $|y|\ge 1$ and for $0<|y|\le 1$. For each complex place $w$, `dC w hw` is an `ArchDatumC (archC w hw)`, the same package over $\mathbb C$ with central law $W(zg)=\chi_{Q_w}(z)\|z\|^2W(g)$ and twists $(u,k)\in\mathbb C\times\mathbb Z$. `dF` is a `FinWhittakerDatum K S Pi`: a function $W_f$ on the adelic group depending only on the finite part of its argument, invariant under right translation by $\mathrm{GL}_2(K_v)$ for $v\in S$, satisfying $W_f(n_v(x)g)=\psi_{K,v}(x)W_f(g)$ and right $\mathrm{GL}_2(\mathcal O_v)$-invariance for $v\notin S$, a Hecke coset eigenvalue equation with eigenvalue $a_v$ at each $v\notin S$ for every level $M$ not divisible by $v$, the central eigenvalue equation with eigenvalue $(Nv)^{-1}b_v$ at each $v\notin S$, and right invariance under some nonzero level subgroup. The hypotheses `hnvR`, `hnvC`, `hnvF` require each `(dR w hw).W`, each `(dC w hw).W` and `dF.Wf` to be nonzero at some invertible matrix, respectively at some adelic point.
--
--   **Niceness.** `hnice` is `IsJLNice K S epsS ω d Π^u archR archC`: there is a system `R : SOrderReps K S` of representatives of the $S$-orders such that for every idele character $\mu$ with `IsJLTwist K S epsS μ` and every choice of archimedean exponents and parameters $(u_w,a_w)$ at the real places and $(u_w,k_w)$ at the complex places satisfying `IsArchCompAt K μ w` with those values, the datum $D=$ `twistedDatum K Π^u S archR archC μ uR aR uC kC` is well formed and convergent, and there exist $\sigma_0\in\mathbb R$ and entire functions $\Lambda,\tilde\Lambda$ on $\mathbb C$, both bounded on vertical strips, such that for $\Re s>\sigma_0$ the series $\sum_n d.a(R.\mathrm{rep}\,n)\,\mathrm{sWeight}(\mu)(R.\mathrm{rep}\,n,s)$ and $\sum_n d.\tilde a(R.\mathrm{rep}\,n)\,\mathrm{sWeight}((\omega\mu)^{-1})(R.\mathrm{rep}\,n,s)$ converge and $\Lambda(s)=d.\mathrm{sSum}\,s\cdot D.\mathrm{archFactor}\,s\cdot D.L(s)$, $\tilde\Lambda(s)=d.\mathrm{sSumDual}\,s\cdot D.\mathrm{archFactorDual}\,s\cdot D.L^{\vee}(s)$, and such that for all $s$,
--   $$\Lambda(s)=d.\mathrm{sFactor}(\mu,s)\cdot \mathrm{pinnedRootNumber}\cdot (\text{finite conductor of }\mu)^{1/2-s}\cdot\tilde\Lambda(1-s).$$
--
--   **Non-Eisenstein hypothesis.** `hnonEis` requires that for no pair $\mu_1,\mu_2$ of continuous characters of the idele group trivial on $K^\times$ does $\Pi^{u}$ agree, outside some finite set of finite places, with the Eisenstein table `eisensteinTableOf K Π.level _ μ₁ μ₂`, whose $a$-value at $v$ is $\mu_1(\varpi_v)+\mu_2(\varpi_v)$ and whose $b$-value is $\mu_1(\varpi_v)\mu_2(\varpi_v)$, the $\varpi_v$ being the uniformizer ideles.
--
--   **Conclusion.** Write $\mathcal P$ for the carrier pins `productionPinsOf K D U gen (adelicBox K)`, where $D=\bigcup_{x\in T}\{h\,x : h\in \mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\}$ (the Siegel set consisting of those $g$ with integral finite part, local height $\ge c$ at every infinite place, $x$-window square $\le u^2$ at every infinite place, and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every infinite place), $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, $\mathrm{gen}(v)=\mathrm{heckeGen}(v)$, with Haar measure on $\mathrm{GL}_2$ of the adeles, central subgroup $Z=\top$, and with $\nu$ the additive Haar measure conditioned on the adelic box. Then there exists a Hecke eigensystem $\Phi'$ over $K$ with complex values such that the following five assertions hold.
--
--   (i) `IsArithGenuineCuspRealizable K 𝒫 Φ'`: there is a `SmoothCuspRealizationAt K 𝒫 Φ'.toRawCentral` (a function on the adelic group, nonzero somewhere, with a central character on $Z$, smooth and cuspidal automorphic in the sense of `IsSmoothCuspAutomorphicFnAt`, invariant under $U(\Phi'.\mathrm{level})$, and, outside a finite exceptional set of finite places, a Hecke coset eigenfunction with eigenvalue $\Phi'.a_v$ and a central eigenfunction with eigenvalue $(Nv)^{-1}\Phi'.b_v$) whose underlying function is continuous.
--
--   (ii) $\Pi$ and $\Phi'$ agree away from a finite set of finite places: there is a finite set outside which $a_v=\Phi'.a_v$ and $b_v=\Phi'.b_v$.
--
--   (iii) There is a realisation $R$ as in (i), with continuous underlying function, and an adelic point $g_0$ such that: the Whittaker coefficient of $R$ with respect to the standard adelic additive character and $\alpha=1$, namely $g\mapsto\int R(n(x)g)\,\overline{\psi}(x)\,d\nu(x)$ with $\nu$ the conditioned measure on the adelic box, is nonzero at some $g$ with the same finite part as $g_0$; and there is $z\in\mathbb C$ such that for every $g$ with the same finite part as $g_0$ this Whittaker coefficient equals
--   $$\Big(\prod_{w\mid\infty}\mathrm{archDetNorm}_w(g)^{\mathrm{mult}(w)}\Big)^{-1/2}\cdot \mathrm{archW}(\mathrm{archR},\mathrm{archC},dR,dC)(g)\cdot z,$$
--   where `archW` is the product over infinite places of $(dR\,w).W$ applied to the real component, respectively $(dC\,w).W$ applied to the complex component, of $g$.
--
--   (iv) For every family of integers $k_w$ indexed by the real places: if each $(dR\,w).W$ satisfies $W(x r)=\mathrm{archWeightChar}_{\mathbb R}(k_w)(r)\,W(x)$ for all $x\in \mathrm{GL}_2(\mathbb R)$ and all $r$ in the subgroup `rowIsometrySubgroup₀ ℝ`, then there is a realisation $R$ of $\Phi'.\mathrm{toRawCentral}$ over $\mathcal P$ with continuous underlying function such that for every real place $w$, every $r$ in `rowIsometrySubgroup₀` of the completion $K_w$ and every adelic $g$,
--   $$R\big(g\cdot \iota_w(r)\big)=\big(\rho_w(r_{00})+\rho_w(r_{01})\,i\big)^{k_w}\,R(g),$$
--   where $\iota_w$ is the inclusion `adelicArchGLInclAt K w` and $\rho_w$ is the isomorphism $K_w\cong\mathbb R$ attached to the real place, viewed in $\mathbb C$.
--
--   (v) For every such family $k_w$, subject to the same right transformation law for the $(dR\,w).W$ and in addition to the holomorphy condition that for every real place $w$ and every $x\in\mathrm{GL}_2(\mathbb R)$ the function $z\mapsto (\Im z)^{-1}\,(dR\,w).W\big(x\cdot \mathrm{iwasawaSectionGL}(z)\big)$ is differentiable on the upper half-plane, there is a realisation $R$ of $\Phi'.\mathrm{toRawCentral}$ over $\mathcal P$ with continuous underlying function, and a realisation $R'$ over $\mathcal P$ of `(Φ'.twist (fun v => (Nv)^(-1/2))).toRawCentral` (the eigensystem with $a$-values $(Nv)^{-1/2}\Phi'.a_v$ and $b$-values $(Nv)^{-2}\Phi'.b_v$), such that: $R'(g)=R(g)\cdot \mathrm{ideleNorm}(\det g)^{1/2}$ for all adelic $g$; the underlying function of $R'$ is continuous; at every real place $w$ the function $R'$ satisfies the predicate `HasArchCharacterAt₀ K w (archWeightCharAt hw (k w hw))`, the transformation law at $w$ under the $k_w$-th power of the character `archWeightOneAt hw` of the row-isometry subgroup; and at every real place $w$ the function $R'$ is archimedean-holomorphic in the sense of `IsArchHolomorphicAt`: for every adelic $g$ the map $z\mapsto (\Im z)^{-1}R'\big(g\cdot\iota_w(\mathrm{iwasawaSectionGL}(z))\big)$ is differentiable on the upper half-plane.
--
--   This is the construction half of the converse theorem for $\mathrm{GL}_2$ over a number field: from a family of $L$-functions with the expected analytic continuation, boundedness in strips and functional equations (packaged as `IsJLNice`), together with prescribed archimedean and finite Whittaker data and the exclusion of Eisenstein eigensystems, it produces a genuine cuspidal realisation with the given Whittaker expansion, weight behaviour at the real places and holomorphy. It is the analytic input to the Langlands–Tunnell step and is used by the statements that specialise it to pinned data and generic central characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_of_isJLNice.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_of_isJLNice
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁)
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
    (hnvR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (hnvC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ g : GL (Fin 2) ℂ, (dC w hw).W g ≠ 0)
    (hnvF : ∃ g, dF.Wf g ≠ 0)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (hnonEis : ∀ (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
      IsIdeleClassChar (𝓞 K) K μ₁ → IsIdeleClassChar (𝓞 K) K μ₂ →
      Continuous μ₁ → Continuous μ₂ →
      ¬ HeckeEigensystem.AgreesAwayFromFinite
          (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (eisensteinTableOf K Pi.level Pi.level_ne_bot μ₁ μ₂)) :
    ∃ Φ' : HeckeEigensystem K ℂ,
      IsArithGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        Φ' ∧
        HeckeEigensystem.AgreesAwayFromFinite Pi Φ' ∧
        (∃ R : SmoothCuspRealizationAt K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K))
            Φ'.toRawCentral,
          IsGenuineCuspRealizationAt K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K))
              Φ'.toRawCentral R ∧
            ∃ g₀ : AdelicGL2 (𝓞 K) K,
              (∃ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ ∧
                whittakerCoefficient K
                    (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                      (adelicBox K))
                    (NumberField.StandardAddChar.stdAddChar K) R.toFun 1 g ≠ 0) ∧
              ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ →
                whittakerCoefficient K
                    (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                      (adelicBox K))
                    (NumberField.StandardAddChar.stdAddChar K) R.toFun 1 g =
                  (((∏ w : InfinitePlace K, NumberField.AdelicVolume.archDetNorm w g ^ w.mult) ^ (-(1 / 2 : ℝ)) :
                        ℝ) : ℂ) *
                    archW archR archC dR dC g * z) ∧
        (∀ k : (w : InfinitePlace K) → w.IsReal → ℤ,
          (∀ (w : InfinitePlace K) (hw : w.IsReal) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
              (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
                (archWeightCharℝ (k w hw) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)) →
            ∃ R : SmoothCuspRealizationAt K
                (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                  (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                  (adelicBox K))
                Φ'.toRawCentral,
              IsGenuineCuspRealizationAt K
                  (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                    (adelicBox K))
                  Φ'.toRawCentral R ∧
                ∀ (w : InfinitePlace K) (hw : w.IsReal) (r : rowIsometrySubgroup₀ w.Completion)
                  (g : AdelicGL2 (𝓞 K) K),
                  R.toFun (g * adelicArchGLInclAt K w (r : GL (Fin 2) w.Completion)) =
                    ((InfinitePlace.Completion.ringEquivRealOfIsReal hw
                          (((r : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0) : ℂ) +
                        (InfinitePlace.Completion.ringEquivRealOfIsReal hw
                            (((r : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 0 1) : ℂ) *
                          Complex.I) ^ (k w hw) *
                      R.toFun g) ∧
        (∀ k : (w : InfinitePlace K) → w.IsReal → ℤ,
          (∀ (w : InfinitePlace K) (hw : w.IsReal) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
              (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
                (archWeightCharℝ (k w hw) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)) →
          (∀ (w : InfinitePlace K) (hw : w.IsReal) (x : GL (Fin 2) ℝ),
              MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) fun z : UpperHalfPlane =>
                ((z.im : ℝ) : ℂ)⁻¹ *
                  (dR w hw).W ((x * iwasawaSectionGL z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) →
            ∃ R : SmoothCuspRealizationAt K
                (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                    (adelicBox K))
                Φ'.toRawCentral,
              IsGenuineCuspRealizationAt K
                  (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                      (adelicBox K))
                  Φ'.toRawCentral R ∧
              ∃ R' : SmoothCuspRealizationAt K
                (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                    (adelicBox K))
                (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).toRawCentral,
              (∀ g : AdelicGL2 (𝓞 K) K,
                  R'.toFun g = R.toFun g * (((ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (1 / 2 : ℝ) : ℝ) : ℂ)) ∧
              IsGenuineCuspRealizationAt K
                  (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
                      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                      (adelicBox K))
                  (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).toRawCentral R' ∧
                (∀ (w : InfinitePlace K) (hw : w.IsReal),
                    HasArchCharacterAt₀ K w (archWeightCharAt hw (k w hw)) R'.toFun) ∧
                ∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchHolomorphicAt w hw R'.toFun) := by sorry
