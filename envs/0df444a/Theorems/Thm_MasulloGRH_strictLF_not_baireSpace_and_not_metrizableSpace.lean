-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_not_baireSpace_and_not_metrizableSpace
-- name    : MasulloGRH.strictLF_not_baireSpace_and_not_metrizableSpace
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:56.892279+00:00
-- url     : https://prove2.me/theorems/15a3e8c4-5ef8-455d-9304-91f9ca2ca894
-- title:
--   Remark C.1.3.3 — a strict LF-space none of whose steps is the whole space is not metrizable (and not a Baire space)
-- statement:
--   **Proper strict LF-spaces are not metrizable (Remark C.1.3.3).** Let $E$ be a strict LF-space with defining sequence $(E_n)_{n\ge 0}$: $E$ is a complex vector space with a topology, $E_0\subset E_1\subset\cdots$ is an increasing sequence of linear subspaces with $E=\bigcup_n E_n$, each $E_n$ is a Fréchet space for the topology induced from $E$, and the topology of $E$ is the finest locally convex topology for which all inclusions $E_n\to E$ are continuous. Assume that no step is the whole space:
--   $$E_n\neq E\qquad\text{for every }n\ge 0$$
--   (this holds in particular if $E_n\ne E_{n+1}$ for all $n$, the form of the hypothesis in the source). Then:
--
--   1. $E$ is not a Baire space;
--   2. $E$ is not metrizable.
--
--   The source states the non-metrizability in Remark C.1.3.3. This explains why the Schwartz–Bruhat spaces $\mathcal S(G)$ of the source (for $G$ an adele ring, an idele class group, or a non-archimedean local field) are not metrizable and have to be treated with nets rather than sequences.
--
--   **Deviation from the source.** The source asserts only non-metrizability, under the hypothesis $E_n\ne E_{n+1}$ for all $n$; the statement uses the weaker hypothesis $E_n\ne E$ for all $n$ and adds the classical sharper conclusion that $E$ is not a Baire space.
--
--   **Formalization Note.** The hypotheses are exactly the data of `MasulloGRH.IsStrictLF E` with an explicit defining sequence `X`; `IsFrechet (X n)` refers to the subspace topology. The properness hypothesis is `X n ≠ ⊤` for all `n`; if some step equals `E` the conclusion fails (then `E` is a Fréchet space).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 660, Remark C.1.3.3 (third paragraph); the paper derives it from H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, 6.6 and from its Lemma C.1.5.4

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_not_baireSpace_and_not_metrizableSpace (E : Type*) [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (hproper : ∀ n, X n ≠ ⊤) :
    ¬ BaireSpace E ∧ ¬ TopologicalSpace.MetrizableSpace E := by sorry

end MasulloGRH
