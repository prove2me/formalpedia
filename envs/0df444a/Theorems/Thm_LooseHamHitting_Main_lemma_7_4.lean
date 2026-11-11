-- Prove2me | Theorems.Thm_LooseHamHitting_Main_lemma_7_4
-- name    : LooseHamHitting.Main.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:57.27281+00:00
-- url     : https://prove2.me/theorems/8e4a6c0b-5eac-45b0-a65b-3a836c3d3bb5
-- title:
--   Lemma 7.4 — degree, codegree and low-degree-set bounds for F∗ ∼ Unif Ω(n, m, ℓ), and the vertex-deletion deficit bound
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $(n,m,\ell)$ be admissible and near-critical, $F_*$ uniform on $\Omega(n,m,\ell)$, and $B_*=\{v:d_{F_*}(v)\le0.03\log n\}$. With probability $1-o(1)$, where the $o(1)$ depends only on $n$:
--
--   (i) $\Delta_1(F_*)\le C\log n$, $|B_*|\le n^{1/4}$ and $\Delta_2(F_*)\le2$; and
--
--   (ii) for every $y\in[n]$, $\sum_{v\in B_*\setminus\{y\}}d_{F_*}(y,v)\le1$.
--
--   (iii) For every fixed integer $h\ge0$, if $n$ is sufficiently large in terms of $h$ and (i), (ii) hold, then every $Z\subseteq[n]$ with $|Z|\le h$ satisfies
--   $$D_Z(F_*,\ell)=\sum_{v\notin Z}\max\{0,\ell_v-d_{F_*-Z}(v)\}\le|Z|.$$
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1), the o(1) depending only on n → ∃ ε : ℕ → ℝ with ε → 0 and P[(i) ∧ (ii) fails] ≤ ε n for all admissible near-critical (n, m, ℓ); reason: explicit null sequence, uniform over m and ℓ
--   - encoding: (iii) for the random F∗ → (iii) for every F ∈ Ω(n, m, ℓ) satisfying (i) and (ii), with ∀ h ∃ N; reason: (iii) is deterministic; F∗ ranges over Ω(n, m, ℓ)
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 28, Lemma 7.4

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process
import Definitions.Def_LooseHamHitting_Main_Core

set_option autoImplicit false

open Classical Filter Topology

namespace LooseHamHitting.Main

/-- Lemma 7.4: degree, codegree and low-degree-set bounds for `F∗ ∼ Unif Ω(n, m, ℓ)` (with one
absolute constant `C` and a failure probability `ε n → 0` depending only on `n`), and the
deterministic vertex-deletion deficit bound (iii). `B∗ = lowDegreeSet n F`. -/
theorem lemma_7_4 :
    ∃ C : ℝ, 0 < C ∧
      (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ (n m : ℕ) (ℓ : Fin n → ℕ), Admissible n m ℓ → NearCritical n m ℓ →
          uniformProb (Omega n m ℓ) (fun F =>
            ¬ (((maxDegree Finset.univ F : ℝ) ≤ C * Real.log n ∧
                ((lowDegreeSet n F).card : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) ∧
                maxCodegree Finset.univ F ≤ 2) ∧
              ∀ y : Fin n, ∑ v ∈ (lowDegreeSet n F).erase y, codegree F y v ≤ 1)) ≤ ε n) ∧
      ∀ h : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (m : ℕ) (ℓ : Fin n → ℕ),
        Admissible n m ℓ → NearCritical n m ℓ → ∀ F ∈ Omega n m ℓ,
          ((maxDegree Finset.univ F : ℝ) ≤ C * Real.log n ∧
            ((lowDegreeSet n F).card : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) ∧
            maxCodegree Finset.univ F ≤ 2) →
          (∀ y : Fin n, ∑ v ∈ (lowDegreeSet n F).erase y, codegree F y v ≤ 1) →
          ∀ Z : Finset (Fin n), Z.card ≤ h → deficit Finset.univ F ℓ Z ≤ Z.card := by sorry

end LooseHamHitting.Main
