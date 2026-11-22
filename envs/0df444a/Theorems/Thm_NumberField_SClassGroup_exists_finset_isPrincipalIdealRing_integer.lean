-- Prove2me | Theorems.Thm_NumberField_SClassGroup_exists_finset_isPrincipalIdealRing_integer
-- name    : NumberField.SClassGroup.exists_finset_isPrincipalIdealRing_integer
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:33.058582+00:00
-- url     : https://prove2.me/theorems/7dd11cd6-0192-49d3-8165-02f53ecaf362
-- title:
--   Remark A.1.5.3 — every finite set $S$ of primes can be enlarged to a finite $T$ with $\mathcal O_{F,T}$ a principal ideal domain ($\mathrm{Pic}(\mathcal O_{F,T})=1$)
-- statement:
--   **Enlarging $S$ until the ring of $S$-integers is a principal ideal domain** (Remark A.1.5.3 of the source).
--
--   Let $F$ be a number field with ring of integers $\mathcal O_F$, and let $S$ be a finite set of nonzero prime ideals of $\mathcal O_F$. Then there is a finite set $T\supseteq S$ of nonzero prime ideals of $\mathcal O_F$ such that the ring of $T$-integers
--   $$\mathcal O_{F,T}=\{x\in F:\ \operatorname{ord}_{\mathfrak p}(x)\ge 0\ \text{for all }\mathfrak p\notin T\}$$
--   is a principal ideal domain; in particular
--   $$\operatorname{Pic}(\mathcal O_{F,T})=1.$$
--
--   This is a consequence of the finiteness of the ideal class group of $\mathcal O_F$, and it is the standard device for reducing a question to class number one. The paper invokes it as "choosing $S'$ large enough so as to arrange $\operatorname{Pic}(\mathcal O_{F,S'})=1$", in order to pass from the exact sequence (A.1.5.9) to the isomorphism (A.1.5.10), $\big(\prod_{v\in S_f}F_v^\times/\mathcal O_{F_v}^\times\big)/\mathcal O_{F,S}^\times\cong\operatorname{Pic}(\mathcal O_F)$.
--
--   **Formalization Note.** $\mathcal O_{F,T}$ is Mathlib's `Set.integer`. A finite set of places containing the Archimedean places, as in the source, is represented by the finite set of its finite places. Both `IsPrincipalIdealRing` and the triviality of `CommRing.Pic` are asserted, so that the statement can be combined directly with statements phrased with either notion.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 544–545, Remark A.1.5.3 (with eq. (A.1.5.10))

import Mathlib

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace NumberField.SClassGroup

theorem exists_finset_isPrincipalIdealRing_integer (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T ∧
      IsPrincipalIdealRing ((T : Set (HeightOneSpectrum (𝓞 F))).integer F) ∧
      Subsingleton (CommRing.Pic ((T : Set (HeightOneSpectrum (𝓞 F))).integer F)) := by sorry

end NumberField.SClassGroup
