-- Prove2me | Theorems.Thm_NumberField_IdeleTopology_idele_topology_not_induced_from_adeles
-- name    : NumberField.IdeleTopology.idele_topology_not_induced_from_adeles
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:30.028241+00:00
-- url     : https://prove2.me/theorems/15f79481-3934-4619-abd6-3461e3caf292
-- title:
--   §A.1.3.1 — the idelic topology is not induced from the adeles: inversion on $\mathbb A_F^\times\subset\mathbb A_F$ is discontinuous and $\mathbb A_F^\times$ has empty interior
-- statement:
--   **The idelic topology is not the topology induced from the adeles** (§A.1.3.1 of the source).
--
--   Let $F$ be a number field, $\mathbb A_F$ its adele ring and $\mathbb A_F^\times$ the group of units of $\mathbb A_F$. The idele group $\mathrm{GL}_1(\mathbb A_F)$ is the group $\mathbb A_F^\times$ with the idelic topology, i.e. the topology induced from $\mathbb A_F\times\mathbb A_F$ by $x\mapsto(x,x^{-1})$. Then:
--
--   1. The continuous injective inclusion $\mathrm{GL}_1(\mathbb A_F)\to\mathbb A_F$ is not a topological embedding: the idelic topology is strictly finer than the subspace topology of $\mathbb A_F^\times\subset\mathbb A_F$.
--   2. For the subspace topology on $\mathbb A_F^\times\subset\mathbb A_F$, the inversion $x\mapsto x^{-1}$ is not continuous; hence $\mathbb A_F^\times$ is not a topological group for that topology.
--   3. $\mathbb A_F^\times$ is not open in $\mathbb A_F$; in fact
--   $$\operatorname{int}\big(\mathbb A_F^\times\big)=\varnothing .$$
--
--   Statements 2 and 3 are the two facts by which the paper motivates Definition A.1.3.1, the re-topologization of $\mathbb A_F^\times$; statement 1 is the same phenomenon expressed in terms of the idelic topology. They explain why the ideles are not treated as a subspace of the adeles anywhere in the adelic constructions of the paper.
--
--   **Formalization Note.** Mathlib's topology on the units `Mˣ` of a topological monoid is by definition the one induced by $x\mapsto(x,x^{-1})$, so statement 1 is the failure of `Topology.IsInducing Units.val`. In statement 2, `Ring.inverse` is the inverse on units, and `ContinuousOn` on the set of units is continuity for the subspace topology. In statement 3 the source only says "not open"; empty interior is the sharper standard fact, and it implies "not open" because the set of units is nonempty. In particular `IsOpenUnits (AdeleRing (𝓞 F) F)` fails, which is the non-example mentioned in the documentation of Mathlib's `IsOpenUnits`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 541, §A.1.3.1 (paragraph before Definition A.1.3.1); classical reference, as cited by the paper at this spot: [CF] J. W. S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. II, §16; [DE] A. Deitmar, S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, §13.3

import Mathlib

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace NumberField.IdeleTopology

theorem idele_topology_not_induced_from_adeles (F : Type*) [Field F] [NumberField F] :
    ¬ Topology.IsInducing (Units.val : (AdeleRing (𝓞 F) F)ˣ → AdeleRing (𝓞 F) F) ∧
    ¬ ContinuousOn (Ring.inverse : AdeleRing (𝓞 F) F → AdeleRing (𝓞 F) F)
        {a : AdeleRing (𝓞 F) F | IsUnit a} ∧
    interior {a : AdeleRing (𝓞 F) F | IsUnit a} = ∅ := by sorry

end NumberField.IdeleTopology
