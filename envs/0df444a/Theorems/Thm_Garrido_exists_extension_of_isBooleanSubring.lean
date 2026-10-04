-- Prove2me | Theorems.Thm_Garrido_exists_extension_of_isBooleanSubring
-- name    : Garrido.exists_extension_of_isBooleanSubring
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T22:40:18.239588+00:00
-- url     : https://prove2.me/theorems/f9d14432-d2b7-4276-8506-0a8c037323f0
-- title:
--   Garrido, Theorem 2.6 (recalled) — a finitely additive measure on a subring of a boolean algebra extends to the whole algebra
-- statement:
--   For every boolean algebra $\mathcal A$, every subring $\mathcal R$ of it (`IsBooleanSubring`) and every finitely additive $\mu$ on $\mathcal R$ with values in $[0, \infty]$ (`IsFinitelyAdditiveOn R μ`), there is a finitely additive $\bar\mu$ on all of $\mathcal A$ (`IsFinitelyAdditiveOn Set.univ μbar`) that agrees with $\mu$ on $\mathcal R$.
--
--   Garrido's Theorem 2.6 (p. 7) opens by recalling this: “**Theorem 2.6** (Invariant Extension Theorem). *Recall Carathéodory’s Extension Theorem: If $\mathcal R$ is a subring of the boolean algebra $\mathcal A$ and $\mu$ is a measure on $\mathcal R$, then $\mu$ can be extended to a measure $\bar\mu$ on $\mathcal A$.* *If $G$ is an amenable group of automorphisms of $\mathcal A$ and $\mathcal R$, $\mu$ are $G$-invariant, then $\bar\mu$ can be chosen to be $G$-invariant.*” This statement is its first sentence, the finitely additive extension the notes call Carathéodory's Extension Theorem. For the algebra of all subsets of a set and a ring of sets it is the published [`FinitelyAdditive.exists_extension_of_isSetRing`](https://prove2.me/theorems/f5d887ac-da22-470b-b85e-ffb4d158b540); a general boolean algebra reduces to that case through its Stone representation, which is not formalized here.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Theorem 2.6 (the recalled Carathéodory Extension Theorem); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_BooleanExtension

namespace Garrido

theorem exists_extension_of_isBooleanSubring {A : Type*} [BooleanAlgebra A] (R : Set A)
    (hR : IsBooleanSubring R) (μ : A → ENNReal) (hμ : IsFinitelyAdditiveOn R μ) :
    ∃ μbar : A → ENNReal, IsFinitelyAdditiveOn Set.univ μbar ∧ ∀ r ∈ R, μbar r = μ r := by
  sorry

end Garrido
