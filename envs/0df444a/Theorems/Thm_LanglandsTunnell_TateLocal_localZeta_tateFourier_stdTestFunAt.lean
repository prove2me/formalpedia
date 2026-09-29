-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt
-- name    : LanglandsTunnell.TateLocal.localZeta_tateFourier_stdTestFunAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/b0395d49-6a31-5013-975d-3bead0c69167
-- title:
--   Ramified local ε-factor: Tate zeta integral of the standard test function
-- statement:
--   Let $K$ be a number field, $v$ a maximal ideal of $\mathcal O_K$ with completion $K_v$ carrying its valuation $\mathrm{v}$ with values in $\{0\}\cup\exp(\mathbb Z)$, and let $\chi\colon K_v^\times\to\mathbb C^\times$ be a homomorphism of groups. Let $a\in\mathbb N$ with $a\ge 1$ and assume `HasConductorExponentAt K v χ a`, i.e. $\chi$ is trivial on $\{u\in K_v^\times : \mathrm v(u)=1,\ \mathrm v(u-1)\le\exp(-a)\}$ while for every $m<a$ the corresponding group at level $m$ (for $m=0$ simply $\mathrm v(u)=1$) contains a unit on which $\chi$ is non-trivial. Let $s\in\mathbb C$ satisfy the convergence condition $\|\chi^{-1}(\varpi_v)\,(Nv)^{-(1-s)}\|<1$, where $\varpi_v=$ `uniformizerUnit K v` and $Nv=$ `Ideal.absNorm v.asIdeal`. Equip $K_v$ with its Borel $\sigma$-algebra and the measure $\mu=$ `selfDualHaarAt K v`, the Haar measure of $\mathcal O_v$ scaled by $(Nv)^{-n/2}$, where $n=$ `addCharLevel` of $\psi=$ `psiLocal K v`, the local component at $v$ of the standard additive character of the adeles of $K$, and $n$ is the supremum of those $k\in\mathbb Z$ with $\psi$ trivial on $\{\mathrm v(x)\le\exp k\}$. Write $\hat f(y)=\int f(x)\psi(xy)\,d\mu(x)$, and $Z(\mu,f,\eta,s)=\int f(x)\,\eta(x)\,|x|^s\,d^\times x$ with $\eta$ extended by $0$ at $0$, $|x|$ the module of multiplication by $x$ and $d^\times x=|x|^{-1}d\mu(x)$ on $K_v\setminus\{0\}$. Then, with $f=$ `stdTestFunAt K v χ` (the indicator of $\mathcal O_v$ if $\chi$ has conductor exponent $0$, otherwise the indicator of the image in $K_v$ of the unit group of level `conductorExponentAt K v χ`), $$Z\bigl(\mu,\hat f,\chi^{-1},1-s\bigr)=\mu\bigl(U^{(a)}\bigr)\,\chi(\varpi_v)^{\,n+a}\,\bigl((Nv)^{\,n+a}\bigr)^{1-s}\int_{\mathrm v(u)=1}\psi\bigl(\varpi_v^{-(n+a)}u\bigr)\chi^{-1}(u)\,d\mu(u),$$ where $U^{(a)}$ denotes the image in $K_v$ of the level-$a$ unit group and $\mu(U^{(a)})$ its real-valued measure.
--
--   This is Tate's local functional-equation computation at a ramified finite place in the standard (self-dual) normalisation: the zeta integral of the Fourier transform of the standard test function attached to $\chi$ is expressed through the volume of the congruence unit group, the factor $\chi(\varpi_v)^{n+a}(Nv)^{(n+a)(1-s)}$ and a Gauss sum of $\chi^{-1}$ against $\psi$, which is the numerator of the local $\varepsilon$-factor. It feeds the local computations of zeta integrals and $L$-factors used in the cubic-induction part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_localZeta_tateFourier_stdTestFunAt.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.StandardAddChar

theorem LanglandsTunnell.TateLocal.localZeta_tateFourier_stdTestFunAt (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (s : ℂ)
    (hs : ‖(χ⁻¹ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))‖ < 1) :
    letI := localBorel K v
    localZeta (selfDualHaarAt K v)
        (tateFourier (psiLocal K v) (selfDualHaarAt K v) (stdTestFunAt K v χ)) χ⁻¹ (1 - s)
      = (((selfDualHaarAt K v).real
            (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) : ℝ) : ℂ)
          * (χ (uniformizerUnit K v) : ℂ) ^ (addCharLevel (psiLocal K v) + a : ℤ)
          * ((((Ideal.absNorm v.asIdeal : ℝ) ^ (addCharLevel (psiLocal K v) + a : ℤ) : ℝ) : ℂ)) ^ (1 - s)
          * ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
              psiLocal K v
                  (((uniformizerUnit K v ^ (-(addCharLevel (psiLocal K v) + a : ℤ)) : (v.adicCompletion K)ˣ) :
                      v.adicCompletion K) * u)
                * charExt χ⁻¹ u ∂(selfDualHaarAt K v) := by sorry
