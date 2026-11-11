-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_lemma_6_9
-- name    : HDXNbhdPCP.Main.lemma_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:44.680543+00:00
-- url     : https://prove2.me/theorems/b30e49b7-850c-4d8c-bf05-a32ea8c38ba3
-- title:
--   Lemma 6.9 — structure and expansion of the KMS complex $A_{q,d,s}$
-- statement:
--   There are absolute constants $q_0,\beta_0>0$ (and an absolute constant $K_1$ for the $O(\cdot)$) such that for every $d\ge3$, $s\ge d$, every prime power $q\ge q_0$ and every irreducible $\mu\in\mathbb F_q[t]$ of degree $s$, the KMS complex $A=A_{q,d,s}$ (colours $\mathbb Z_{d+1}$) satisfies:
--
--   1. **Local spectral expansion.** $A$ is a $K_1\,d\,q^{-1/2}$-product.
--   2. **Vertex links.** For every $i\in\mathbb Z_{d+1}$ and $v\in A[i]$, the link $A_v$ with colours renamed by $i+j\mapsto j$ ($j\in[d]$) is isomorphic to $O_\sigma(\mathbb F_q^{d+1})$ for a maximal flag $\sigma$.
--   3. **Regularity.** For every $i$, $A[i,i+1]$ is a balanced $q^d$-regular bipartite graph.
--   4. **Cycle structure.** $A$ is a cycle complex (Definition 2.10).
--   5. **Coboundary expansion.** The colour restriction $A[1,2,3]$ is a $\beta_0$-coboundary expander over $\mathrm{Sym}(m)$ for every $m<\mathrm{char}(\mathbb F_q)$.
--
--   Items 1–2 are from Grave de Peralta and Valentiner-Branth; item 5 is proved in Appendix D. Together they make $A$ a host for the local-to-global theorem.
--
--   Differences from the source:
--   - encoding: G = SL_{d+1}(F_q[t]/(μ)) with μ irreducible of degree s; 'sufficiently large prime power q' → Matrix.SpecialLinearGroup (Fin (d+1)) (AdjoinRoot μ) for every irreducible μ of degree s over a finite field K; |K| ≥ q₀ with q₀ absolute; reason: A_{q,d,s} does not depend on the choice of μ up to isomorphism; the lemma names q₀ as an absolute constant
--   - reading: the facet distribution of the coset complex (not stated) → the image of the uniform distribution on G; reason: uniform on facets: the fibres are cosets of one subgroup
--   - encoding: 'is isomorphic to O_σ(F_q^{d+1})' → IsIsomorphic: colour-preserving maps injective on vertex sets carrying the facet distribution of the renamed link onto that of O_σ, for some maximal flag σ; reason: isomorphism of weighted coloured complexes
--   - encoding: Z_{d+1}; m < char(F_q) (m ≥ 1) → Fin (d+1) with modular addition; every natural m < ringChar K, including m = 0; reason: Sym(0) is trivial, so the added case holds automatically
--   - encoding: O(dq^{-1/2})-product → IsProduct with parameter K₁·d·q^{-1/2}, K₁ > 0 absolute (chosen with q₀, β₀, before d, s, q); reason: explicit constant for the O(·)
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 41, Lemma 6.9 (item 5 proved in Appendix D)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Building

open Polynomial

namespace HDXNbhdPCP.Main

/-- Lemma 6.9: structure and expansion of the KMS complex `A = A_{q,d,s}` (colours `ℤ_{d+1}`). -/
theorem lemma_6_9 :
    ∃ q₀ β₀ : ℝ, 0 < q₀ ∧ 0 < β₀ ∧ ∃ K₁ : ℝ, 0 < K₁ ∧
      ∀ d s : ℕ, 3 ≤ d → d ≤ s →
      ∀ (K : Type) [Field K] [Fintype K], (Fintype.card K : ℝ) ≥ q₀ →
      ∀ (mu : K[X]) (hmu : Irreducible mu), mu.natDegree = s →
        -- 1. local spectral expansion
        (kms K d mu hmu.ne_zero).IsProduct (K₁ * d * (Fintype.card K : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        -- 2. vertex links are opposite complexes
        (∀ (i : Fin (d + 1)) (y : (j : Fin (d + 1)) → KMSGroup K d mu ⧸ kmsH K d mu j),
          y ∈ (kms K d mu hmu.ne_zero).supp →
            ∃ E : BColor (d + 1) → Submodule K (Fin (d + 1) → K), IsMaxFlag K E ∧
              ColoredComplex.IsIsomorphic (kmsLink K d mu hmu.ne_zero i y) (opposite K (d + 1) E)) ∧
        -- 3. regularity
        (∀ i : Fin (d + 1), ((kms K d mu hmu.ne_zero).pairGraph i (i + 1)).IsBalanced ∧
          ((kms K d mu hmu.ne_zero).pairGraph i (i + 1)).IsRegular (Fintype.card K ^ d)) ∧
        -- 4. cycle structure
        (kms K d mu hmu.ne_zero).IsCycleComplex ∧
        -- 5. coboundary expansion of the colour restriction A[1, 2, 3]
        (∀ m : ℕ, m < ringChar K →
          (kms K d mu hmu.ne_zero).HasCobExpOn {1, 2, 3} (Equiv.Perm (Fin m)) β₀) := by sorry

end HDXNbhdPCP.Main
