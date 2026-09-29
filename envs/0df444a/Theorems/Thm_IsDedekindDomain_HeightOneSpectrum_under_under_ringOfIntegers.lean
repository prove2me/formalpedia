-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers
-- name    : IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/e47c8418-817c-5e54-8209-a2d5812bb6d2
-- title:
--   Transitivity of restriction of finite places in a tower
-- statement:
--   Let $K$, $K'$, $K''$ be number fields, so fields of characteristic zero that are finite over $\mathbb{Q}$, together with algebra structures making $K \to K' \to K''$ a tower (an `IsScalarTower K K' K''` hypothesis, so that the composite of the structure maps $K \to K'$ and $K' \to K''$ agrees with the given map $K \to K''$). Let $w''$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_{K''}$, i.e. a nonzero prime ideal of $\mathcal{O}_{K''}$, equivalently a finite place of $K''$. The assertion is that restricting $w''$ first to $\mathcal{O}_{K'}$ and then to $\mathcal{O}_K$ gives the same height-one prime of $\mathcal{O}_K$ as restricting $w''$ directly to $\mathcal{O}_K$: in terms of `HeightOneSpectrum.under`, which takes the contraction (preimage ideal) along the algebra map of the rings of integers, one has $\mathrm{under}_{\mathcal{O}_K}(\mathrm{under}_{\mathcal{O}_{K'}}(w'')) = \mathrm{under}_{\mathcal{O}_K}(w'')$ as elements of the height-one spectrum of $\mathcal{O}_K$.
--
--   This is the transitivity of the lying-over relation $w'' \mid w' \mid w$ for finite places in a tower of number fields. It is used as bookkeeping for places in a tower wherever compatibility of adic completions, of semialgebra maps between them, and of decomposition-group sums along $K \subseteq K' \subseteq K''$ has to be expressed in terms of a single restricted place of $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers.lean

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField

theorem IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) :
    HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'') = HeightOneSpectrum.under (𝓞 K) w'' := by sorry
