-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
-- name    : LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/e0039743-d8aa-5207-878e-bab6fa09c5ad
-- title:
--   Local zeta integral of a ramified standard test function
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal{O}_K$ (a point of `HeightOneSpectrum (𝓞 K)`), and $K_v =$ `v.adicCompletion K` the completion, with its valuation `Valued.v` taking values in $\{0\}\cup\exp(\mathbb{Z})$. Let $\chi : K_v^\times \to \mathbb{C}^\times$ be a group homomorphism, $a$ a natural number with $1 \le a$, and assume `HasConductorExponentAt K v χ a`, i.e. $\chi$ is trivial on `higherUnitsAt K v a` $= \{u : |u|_v = 1,\ |u-1|_v \le \exp(-a)\}$, while for every $m < a$ there is $u$ in `higherUnitsAt K v m` with $\chi(u) \ne 1$. Let $s \in \mathbb{C}$ be arbitrary. Equip $K_v$ with its Borel $\sigma$-algebra. The assertion is that the Tate local zeta integral
--   $$\int_{K_v} f(x)\,\chi^{\mathrm{ext}}(x)\,|x|^{s}\, \mathrm{d}\big((\mu_v|_{\{0\}^{c}}) \cdot |x|^{-1}\big),$$
--   where $\mu_v$ is `selfDualHaarAt K v`, namely $N(v)^{-n/2}$ times the additive Haar measure giving $\mathcal{O}_v$ volume $1$ with $n$ the level `addCharLevel` of the local component `psiLocal K v` of the standard additive character; $|x|$ denotes `modulus x` (the module of multiplication by $x$, $0$ at $0$); $\chi^{\mathrm{ext}}$ is $\chi$ extended by $0$ at $0$; and $f =$ `stdTestFunAt K v χ`, which is the indicator of $\mathcal{O}_v$ when $\chi$ has conductor exponent $0$ and otherwise the indicator of the image in $K_v$ of `higherUnitsAt K v (conductorExponentAt K v χ)` — equals the real-valued $\mu_v$-measure of the image in $K_v$ of `higherUnitsAt K v a`. In particular the value is independent of $s$, and no convergence restriction on $s$ is imposed.
--
--   This is the evaluation, in Tate's local theory at a finite place, of the zeta integral of the standard test function attached to a ramified character: for conductor exponent $a \ge 1$ the integrand reduces to the indicator of $1+\mathfrak{p}_v^a$ and the integral is its self-dual volume. It serves as the denominator in the computation of the local constant of a ramified character, and is used in the local computations of zeta integrals and $L$-factors in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_real_image_higherUnitsAt (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (a : ℕ) (ha : 1 ≤ a)
    (hχ : HasConductorExponentAt K v χ a) (s : ℂ) :
    letI := localBorel K v
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s
      = (((selfDualHaarAt K v).real
            (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v a) : ℝ) : ℂ) := by sorry
