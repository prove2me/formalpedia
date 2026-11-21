-- Prove2me | Theorems.Thm_MasulloGRH_epsTensor_assoc
-- name    : MasulloGRH.epsTensor_assoc
-- status  : Proved
-- author  : @ijawdoij123
-- created : 2026-11-20T22:57:02.135177+00:00
-- url     : https://prove2.me/theorems/f3ece092-c77f-4a36-8d0e-3ff9ff214066
-- title:
--   Associativity of the injective tensor product: $(E\otimes_\varepsilon F)\otimes_\varepsilon G\cong E\otimes_\varepsilon(F\otimes_\varepsilon G)$
-- statement:
--   Throughout, all vector spaces are over $\mathbb C$, and a locally convex space is one whose topology is defined by a family of seminorms. The injective topology $\varepsilon$ on $E\otimes F$ is the topology of uniform convergence on the sets $A\times B$, where $A\subseteq E'$ and $B\subseteq F'$ are equicontinuous sets of continuous linear functionals, a tensor $u$ being regarded as the function $(x',y')\mapsto (x'\otimes y')(u)$ on $E'\times F'$; $E\otimes_\varepsilon F$ denotes $E\otimes F$ with this topology.
--
--   Let $E$, $F$, $G$ be Hausdorff locally convex spaces. Then the canonical algebraic isomorphism
--   $$
--   \alpha:(E\otimes F)\otimes G\to E\otimes(F\otimes G),\qquad (x\otimes y)\otimes z\mapsto x\otimes(y\otimes z),
--   $$
--   is a topological isomorphism
--   $$
--   (E\otimes_\varepsilon F)\otimes_\varepsilon G\;\cong\; E\otimes_\varepsilon(F\otimes_\varepsilon G).
--   $$
--   Equivalently, the injective topology of $(E\otimes_\varepsilon F)\otimes G$ is the topology induced by $\alpha$ from the injective topology of $E\otimes(F\otimes_\varepsilon G)$.
--
--   It is one of the basic structural facts about tensor product topologies and is used in proving that the projective tensor product of two nuclear spaces is nuclear.
--
--   **Formalization Note** The statement is the equality of topologies `epsTensorTopology (E ⊗ F) G = induced (TensorProduct.assoc ℂ E F G) (epsTensorTopology E (F ⊗ G))`, where $E\otimes F$ and $F\otimes G$ carry their injective topologies, and duals are the continuous duals `StrongDual`. All three spaces live in the same universe.
-- source:
--   A. Grothendieck, Produits tensoriels topologiques et espaces nucléaires, Mem. AMS 16 (1955), Ch. I, §1, n°3 (associativity of the injective tensor product); H. H. Schaefer, Topological Vector Spaces (GTM 3, 2nd ed.), Ch. III, §6 and the proof of §7.5; F. Trèves, Topological Vector Spaces, Distributions and Kernels, Ch. 43–44. Used in the proof that $E\otimes_\pi F$ is nuclear for nuclear $E,F$ (Masullo, The Music of the Primes, Appendix C, Lemma C.2.4.10(4), p. 689).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

open TensorProduct Topology

universe u

theorem epsTensor_assoc (E F G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hE : IsHLCS E) (hF : IsHLCS F) (hG : IsHLCS G) :
    @epsTensorTopology (E ⊗[ℂ] F) _ _ (epsTensorTopology E F) G _ _ _ =
      TopologicalSpace.induced (TensorProduct.assoc ℂ E F G)
        (@epsTensorTopology E _ _ _ (F ⊗[ℂ] G) _ _ (epsTensorTopology F G)) := by sorry

end MasulloGRH
