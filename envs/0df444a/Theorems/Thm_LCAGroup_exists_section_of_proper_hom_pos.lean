-- Prove2me | Theorems.Thm_LCAGroup_exists_section_of_proper_hom_pos
-- name    : LCAGroup.exists_section_of_proper_hom_pos
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T17:00:46.714265+00:00
-- url     : https://prove2.me/theorems/f25b68ad-025d-4e97-8565-6fdcd5d9205a
-- title:
--   Remark D.2.1.2 — a proper continuous homomorphism $|\cdot|_G\colon G\to\mathbb R_{>0}$ of a locally compact abelian group has a continuous homomorphic section over its image
-- statement:
--   **Splitting of a locally compact abelian group over a proper homomorphism to $\mathbb R_{>0}$** (Remark D.2.1.2).
--
--   Let $G$ be a Hausdorff locally compact abelian group, written multiplicatively, and let
--   $$|\cdot|_G\colon G\longrightarrow\mathbb R_{>0}$$
--   be a continuous homomorphism to the multiplicative group of positive real numbers that is **proper**: the preimage of every compact subset of $\mathbb R_{>0}$ is compact, equivalently $\{g\in G:\ a\le|g|_G\le b\}$ is compact for all $0<a\le b$. (In the source such a pair, with $|\cdot|_G$ non-trivial and $G$ second countable, is called a *modulated group* with *module* $|\cdot|_G$; the examples are the idele class group $C_F$ with the idelic norm and its $S$-variants.) Let $\Gamma=|G|_G\subseteq\mathbb R_{>0}$ be the image, a closed subgroup of $\mathbb R_{>0}$, hence equal to $\{1\}$, to $t^{\mathbb Z}$ for a unique $t>1$, or to $\mathbb R_{>0}$; and let $G^1=\ker|\cdot|_G$, a compact subgroup.
--
--   **Statement.** The homomorphism $|\cdot|_G$ admits a continuous homomorphic section over its image: there is a continuous homomorphism
--   $$\tau\colon\Gamma\longrightarrow G\qquad\text{with}\qquad|\tau(t)|_G=t\quad\text{for all }t\in\Gamma .$$
--
--   As a consequence (not part of the formal statement), $(k,t)\mapsto k\,\tau(t)$ is an isomorphism of topological groups $G^1\times\Gamma\cong G$, depending on the choice of $\tau$; this splitting is what the source uses to build the canonical measure of a modulated group and the decomposition $\mathcal S(G)\cong\mathcal S(G^1)\,\overline\otimes\,\mathcal S(\Gamma)$ (Lemma D.2.2.2). The source refers to the structure theorem for locally compact abelian groups.
--
--   **Formalization Note.** The homomorphism is a function `m : G → ℝ` with `0 < m g`, `m (g * h) = m g * m h`, `Continuous m`, and properness in the form `∀ a b, 0 < a → IsCompact (m ⁻¹' Set.Icc a b)` (the same encoding as the platform definition `MasulloGRH.IsModule`). The section is a function `τ : ℝ → G` whose values outside `Set.range m` are irrelevant: it is continuous on `Set.range m`, multiplicative on `Set.range m`, and satisfies `m (τ t) = t` for `t ∈ Set.range m`. **Deviation from the source.** The remark is made for second countable $G$ and non-trivial $|\cdot|_G$; neither hypothesis is needed (if $|\cdot|_G$ is trivial then $G$ is compact and $\tau=1$), and the statement is given for every Hausdorff locally compact abelian group.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 793, Remark D.2.1.2 (with Definition D.2.1.1); references given in the source at this spot: W. Rudin, Fourier Analysis on Groups, Wiley-Interscience, 1962 (structure theorem for locally compact abelian groups, cited in the source as [Ru, Thm. 1.2.4]), and A. Weil, Sur les "formules explicites" de la théorie des nombres, Izv. Akad. Nauk SSSR Ser. Mat. 36 (1972), 3–18 (listed in the source's bibliography as [Weil-e], with venue given as Proc. Inst. Math. Steklov), §3, pp. 5–6 (for modulated groups)

import Mathlib

set_option autoImplicit false

namespace LCAGroup

theorem exists_section_of_proper_hom_pos (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G → ℝ) (hpos : ∀ g, 0 < m g) (hmul : ∀ g h, m (g * h) = m g * m h)
    (hcont : Continuous m) (hproper : ∀ a b : ℝ, 0 < a → IsCompact (m ⁻¹' Set.Icc a b)) :
    ∃ τ : ℝ → G, ContinuousOn τ (Set.range m) ∧
      (∀ s ∈ Set.range m, ∀ t ∈ Set.range m, τ (s * t) = τ s * τ t) ∧
      ∀ t ∈ Set.range m, m (τ t) = t := by sorry

end LCAGroup
