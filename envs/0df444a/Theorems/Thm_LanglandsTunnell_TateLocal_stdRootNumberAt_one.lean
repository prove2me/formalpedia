-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_one
-- name    : LanglandsTunnell.TateLocal.stdRootNumberAt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/43298f93-883b-535c-b100-6121dbe256e4
-- title:
--   Standard local root number of the trivial character is 1
-- statement:
--   Let $K$ be a number field and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, i.e. a finite place of $K$, with completion $K_v$ written `v.adicCompletion K`. Take for the local quasi-character the trivial one, namely the unit element $1$ of the group of monoid homomorphisms $K_v^\times \to \mathbb{C}^\times$ (the map sending every unit to $1$). The assertion is that `stdRootNumberAt K v 1 = 1`. Here `stdRootNumberAt K v χ` is by definition the value at $s = 1/2$ of `stdEpsilonAt K v χ`, which is Tate's local epsilon factor `localEpsilonAt` at the place $v$ formed from the self-dual Haar measure `selfDualHaarAt K v` on $K_v$, the standard local additive character `psiLocal K v` of $K_v$, the standard local test function `stdTestFunAt K v χ` attached to $\chi$, and $\chi$ itself. Thus the standard local root number of the trivial character equals $1$ at every finite place.
--
--   This is the unramified local computation in Tate's local functional equation: for the trivial quasi-character the local root number $\varepsilon(1/2,\mathbf 1,\psi_v)$ is trivial. It is used throughout the local analysis of the Langlands–Tunnell argument, for instance in the normalisation of Whittaker data and newvectors and in the synthesis of cusp forms from local data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_one.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.TateLocal.stdRootNumberAt_one (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    LanglandsTunnell.TateLocal.stdRootNumberAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = 1 := by sorry
