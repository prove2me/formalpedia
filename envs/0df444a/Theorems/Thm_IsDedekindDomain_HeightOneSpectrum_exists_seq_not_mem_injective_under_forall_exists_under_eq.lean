-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_seq_not_mem_injective_under_forall_exists_under_eq
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_seq_not_mem_injective_under_forall_exists_under_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/f76a4cb9-de75-57ac-bd0b-42dac7f9bee9
-- title:
--   A sequence of primes of 𝒪_L outside a finite set, with injective and exhaustive traces to K
-- statement:
--   Let $K$ and $L$ be number fields (each a field with a `NumberField` structure), with $L$ an algebra over $K$, and let $S_L$ be a finite set of elements of the height-one spectrum of $\mathcal{O}_L$, i.e. of nonzero prime ideals of the ring of integers of $L$. The assertion is the existence of a sequence $\mathfrak{P} : \mathbb{N} \to$ `HeightOneSpectrum (𝓞 L)` with three properties: first, $\mathfrak{P}_k \notin S_L$ for every $k$; second, the map $k \mapsto$ `HeightOneSpectrum.under (𝓞 K) (𝔓 k)`, sending $k$ to the prime of $\mathcal{O}_K$ lying under $\mathfrak{P}_k$ (the contraction of $\mathfrak{P}_k$ along $\mathcal{O}_K \to \mathcal{O}_L$), is injective; and third, for every nonzero prime $w$ of $\mathcal{O}_L$ with $w \notin S_L$ there is an index $k$ with `under (𝓞 K) (𝔓 k) = under (𝓞 K) w`. Thus the sequence picks out, without repetition of the primes below, exactly one prime of $\mathcal{O}_L$ outside $S_L$ above each prime of $\mathcal{O}_K$ that has at least one such prime above it. No compatibility of the $K$-algebra structure on $L$ with the integral closures beyond what Mathlib's `under` requires is assumed, and $L/K$ is not assumed to be an extension of any particular degree.
--
--   This is an elementary re-indexing statement about primes in an extension of number fields: the set of primes of $\mathcal{O}_K$ that are met by primes of $\mathcal{O}_L$ outside a finite set is countably infinite, so such primes may be enumerated by $\mathbb{N}$ with distinct primes below. It is used to re-index unramified places in two automorphic-form constructions on the Langlands–Tunnell side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_seq_not_mem_injective_under_forall_exists_under_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_seq_not_mem_injective_under_forall_exists_under_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ rec : ℕ → HeightOneSpectrum (𝓞 L), (∀ k, rec k ∉ SL) ∧
      (Function.Injective fun k => HeightOneSpectrum.under (𝓞 K) (rec k)) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        ∃ k, HeightOneSpectrum.under (𝓞 K) (rec k) = HeightOneSpectrum.under (𝓞 K) w := by sorry
