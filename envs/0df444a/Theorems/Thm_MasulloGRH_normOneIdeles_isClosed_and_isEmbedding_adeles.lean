-- Prove2me | Theorems.Thm_MasulloGRH_normOneIdeles_isClosed_and_isEmbedding_adeles
-- name    : MasulloGRH.normOneIdeles_isClosed_and_isEmbedding_adeles
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:43:19.473634+00:00
-- url     : https://prove2.me/theorems/990348bc-7bab-4d68-b189-6c2771e4a14c
-- title:
--   The norm-one ideles are closed in $\mathbb A_F$, and the idelic and adelic topologies agree on them (Cassels–Fröhlich, Ch. II, §16)
-- statement:
--   **The norm-one ideles as a subspace of the adeles** (Cassels–Fröhlich, *Algebraic Number Theory*, Ch. II, §16, Lemma). Let $F$ be a number field, $\mathbf A_F$ its adele ring and $\mathrm{GL}_1(\mathbf A_F)=\mathbf A_F^\times$ its idele group with the idelic topology, i.e. the topology induced from $\mathbf A_F\times\mathbf A_F$ by $x\mapsto(x,x^{-1})$. Let
--   $$|g|_F=\prod_{v}|g_v|_v$$
--   be the idelic norm, the product over all places $v$ of $F$ of the normalized absolute values (the usual absolute value at a real place, its square at a complex place, and $|\pi_v|_v=N(\mathfrak p_v)^{-1}$ at a finite place $v$), and let
--   $$\mathrm{GL}_1(\mathbf A_F)^1=\{g\in\mathbf A_F^\times : |g|_F=1\}$$
--   be the group of ideles of norm one. Then:
--   1. $\mathrm{GL}_1(\mathbf A_F)^1$ is a closed subset of $\mathbf A_F$;
--   2. on $\mathrm{GL}_1(\mathbf A_F)^1$ the subspace topology inherited from the idelic topology coincides with the subspace topology inherited from $\mathbf A_F$, i.e. the inclusion $\mathrm{GL}_1(\mathbf A_F)^1\hookrightarrow\mathbf A_F$ is a topological embedding.
--
--   Part 2 contrasts with the situation on the whole of $\mathbf A_F^\times$, where the idelic topology is strictly finer than the topology induced from $\mathbf A_F$. The lemma is the standard first step towards the compactness of $\mathrm{GL}_1(\mathbf A_F)^1/F^\times$. In the paper it is invoked in the proof of Lemma 8.2.0.3(2) (p. 386): it shows that the locus $D^1_1=\{g\in\mathbf A_F^\times:|g|_F=1\}\subset\mathbf A_F$ is closed in $\mathbf A_F$ and that its subspace topology is the topology of $\mathrm{GL}_1(\mathbf A_F)^1$.
--
--   **Formalization Note.** The idele group is `MasulloGRH.IdeleGroup F`, i.e. the units `(AdeleRing (𝓞 F) F)ˣ` with Mathlib's units topology, which is the topology induced by $x\mapsto(x,x^{-1})$; the idelic norm is `MasulloGRH.ideleNorm` from the platform definition `Def_MasulloGRH_IdeleNorm`. Part 1 is the closedness of the image of $\{g:|g|_F=1\}$ under `Units.val`; part 2 is `Topology.IsEmbedding` of `Units.val` restricted to the subtype $\{g:|g|_F=1\}$, which carries the subspace topology of the idele group.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 386, proof of Lemma 8.2.0.3(2); classical reference (as cited by the paper at this spot): J. W. S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. II, §16, Lemma, p. 69

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm

open NumberField IsDedekindDomain Topology

set_option autoImplicit false

namespace MasulloGRH

/-- Lemma of Cassels–Fröhlich, Ch. II, §16: the ideles of norm one form a closed subset of the
adeles, and on them the idelic topology coincides with the topology induced from the adeles. -/
theorem normOneIdeles_isClosed_and_isEmbedding_adeles (F : Type*) [Field F] [NumberField F] :
    IsClosed ((fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F)) '' {g | ideleNorm g = 1}) ∧
      IsEmbedding (fun g : {g : IdeleGroup F // ideleNorm g = 1} =>
        ((g : IdeleGroup F) : AdeleRing (𝓞 F) F)) := by sorry

end MasulloGRH
