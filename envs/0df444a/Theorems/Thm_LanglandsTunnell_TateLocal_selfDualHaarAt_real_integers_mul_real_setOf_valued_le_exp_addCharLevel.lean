-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
-- name    : LanglandsTunnell.TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/c5696ddc-3c67-5055-84b3-067ce53c747c
-- title:
--   Self-dual local Haar measure: μ(mathcal Oᵥ) μ(mathfrak pᵥ⁻ⁿ)=1
-- statement:
--   Let $K$ be a number field and let $v$ be a height-one prime of its ring of integers $\mathcal O_K$, with completion $K_v =$ `v.adicCompletion K` carrying its valuation `Valued.v` into $\{0\}\cup\exp(\mathbb Z)$ and its valuation subring $\mathcal O_v =$ `v.adicCompletionIntegers K`. Here $K_v$ is equipped with its Borel $\sigma$-algebra (`localBorel K v`), $\psi_{K,v} =$ `psiLocal K v` is the additive character of $K_v$ obtained by composing the standard adelic additive character `stdAddChar K` with the additive embedding `adeleSingleAt K v` of $K_v$ into the adele ring of $K$ through the finite adeles, and $n =$ `addCharLevel (psiLocal K v)` is the supremum of the set of integers $m$ such that $\psi_{K,v}$ is trivial on $\{x : |x|_v \le \exp m\}$. Let $\mu =$ `selfDualHaarAt K v` be the additive Haar measure on $K_v$ normalised so that the compact open subgroup $\mathcal O_v$ has measure $1$, rescaled by the factor $(\mathrm N v)^{-n/2}$, where $\mathrm N v =$ `Ideal.absNorm v.asIdeal`. The assertion is the identity of real numbers $$\mu(\mathcal O_v)\cdot\mu(\{x \in K_v : |x|_v \le \exp n\}) = 1,$$ both values being taken via `Measure.real`.
--
--   This is the normalisation property of the self-dual (Tate) local measure at a finite place: the lattice $\mathcal O_v$ and the set $\mathfrak p_v^{-n}$, which for a character of exact level $n$ is the dual lattice of $\mathcal O_v$, have reciprocal volumes. It is used in the local functional equations and epsilon-factor computations of the local Tate theory underlying the cubic induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.StandardAddChar

theorem LanglandsTunnell.TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    (selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K))
        * (selfDualHaarAt K v).real
            {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v))} = 1 := by sorry
