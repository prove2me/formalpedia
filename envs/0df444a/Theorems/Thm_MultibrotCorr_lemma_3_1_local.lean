-- Prove2me | Theorems.Thm_MultibrotCorr_lemma_3_1_local
-- name    : MultibrotCorr.lemma_3_1_local
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-21T15:59:29.642636+00:00
-- url     : https://prove2.me/theorems/6c7fc11a-d501-40e0-88e2-aa4501c05564
-- title:
--   Lemma 3.1, holomorphic motion of a repelling cycle, with holomorphy near $(b,z_j)$
-- statement:
--   Let $(z_i)_0^n$ be a repelling cycle of period $n$ of $\mathbf{f}_b$ with univalent branches $f_i$ sending $z_{i-1}$ to $z_i$, extended $n$-periodically. The return map $h_j=f_{n+j}\circ\cdots\circ f_{j+1}$ has a repelling fixed point at $z_j$. For each $j\in[0,n]$: (i) $(c,z)\mapsto h_{j,c}(z)$ is holomorphic near $(b,z_j)$; (ii) there is a unique holomorphic function $\tilde z_j$ near $b$ with $\tilde z_j(b)=z_j$ and $h_{j,c}(\tilde z_j(c))=\tilde z_j(c)$; (iii) the perturbed branch $f_{j,c}$ sends $\tilde z_{j-1}(c)$ to $\tilde z_j(c)$, and the resulting cycle is repelling. Uniqueness in (ii) is germ uniqueness (any other holomorphic fixed-point selection agrees near $b$).
--
--   **Formalization Note** Part (i) is stated on a product $V_1\times V_2$ of open sets with $b\in V_1$ and $z_j\in V_2$, that is on a neighborhood of $(b,z_j)$ as in the source. The branches `φ i` are total functions that are only constrained on the open sets `U i`, so nothing can be said about the composition near $(b,b)$.
-- source:
--   C. Siqueira, Similarity between the Multibrot set and the Julia set of correspondences at Misiurewicz points, https://arxiv.org/abs/2509.07266, Lemma 3.1, Section 3; eq. (3.1), (3.2), (3.3).

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr
theorem lemma_3_1_local (e : UnicriticalExponent) (b : ℂ) (n : ℕ)
    (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
    (hn : 0 < n)
    (hzper : ∀ i, z (i + n) = z i)
    (hφper : ∀ i, φ (i + n) = φ i)
    (hbranch : ∀ i, IsOpen (U i) ∧ z i ∈ U i ∧ IsUnivalentBranch e 0 (U i) (φ i) ∧
      φ i (z i) + b = z (i + 1))
    (hrep : IsRepellingCycle e b n z) :
    ∃ (W : Set ℂ) (zz : ℕ → ℂ → ℂ),
      IsOpen W ∧ b ∈ W ∧
      (∀ j, DifferentiableOn ℂ (zz j) W ∧ zz j b = z j) ∧
      (∀ j, zz (j + n) = zz j) ∧
      (∀ c ∈ W, ∀ j, perturbedComp e φ j n c (zz j c) = zz j c) ∧
      (∀ c ∈ W, ∀ j, zz (j + 1) c = φ j (zz j c) + c) ∧
      (∀ c ∈ W, IsRepellingCycle e c n (fun j => zz j c)) ∧
      (∀ j, ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ b ∈ V₁ ∧ IsOpen V₂ ∧ z j ∈ V₂ ∧
        DifferentiableOn ℂ (fun p : ℂ × ℂ => perturbedComp e φ j n p.1 p.2) (V₁ ×ˢ V₂)) ∧
      (∀ j, ∀ (w : ℂ → ℂ) (Vw : Set ℂ), IsOpen Vw → b ∈ Vw →
        DifferentiableOn ℂ w Vw → w b = z j →
        (∀ c ∈ Vw, perturbedComp e φ j n c (w c) = w c) →
        ∃ V' : Set ℂ, IsOpen V' ∧ b ∈ V' ∧ V' ⊆ Vw ∧ V' ⊆ W ∧ ∀ c ∈ V', w c = zz j c) := by sorry
end MultibrotCorr
