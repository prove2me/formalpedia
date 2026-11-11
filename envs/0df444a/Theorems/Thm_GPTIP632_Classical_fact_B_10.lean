-- Prove2me | Theorems.Thm_GPTIP632_Classical_fact_B_10
-- name    : GPTIP632.Classical.fact_B_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:48.480673+00:00
-- url     : https://prove2.me/theorems/3dfadf55-2472-4db3-a69c-4a657d27648f
-- title:
--   Fact B.10: composites with a classical factor are unique, with cone $(V_B^+)^{\oplus n}$
-- statement:
--   Let $\Delta_n$ be the classical $n$-level system ($V=\mathbb R^n$, $V^+=\mathbb R^n_{\ge0}$, $u(\omega)=\sum_i\omega_i$) and let $B$ be any system. Identify $\mathbb R^n\otimes V_B$ with $V_B^{\oplus n}$ via $\delta_i\otimes\beta\mapsto(0,\dots,\beta,\dots,0)$. Then
--
--   $$
--   \mathbb R^n_{\ge0}\otimes_{\min}V_B^+=\mathbb R^n_{\ge0}\otimes_{\max}V_B^+=(V_B^+)^{\oplus n}=\Big\{\sum_i\delta_i\otimes\beta_i:\beta_i\in V_B^+\Big\}.
--   $$
--
--   Consequently every composite of $\Delta_n$ with $B$ has the cone $(V_B^+)^{\oplus n}$, and its states are the vectors $\sum_i\delta_i\otimes\beta_i$ with $\beta_i\in V_B^+$ and $\sum_iu_B(\beta_i)=1$: a classical value $i$ occurring with probability $p_i=u_B(\beta_i)\ge0$, together with the conditional state $\beta_i/p_i$ of $B$ when $p_i>0$.
--
--   A composite with a classical factor is therefore forced, whatever the theory: this is what lets classical registers be read without disturbance and what makes channels with classical registers decompose (Fact B.13).
--
--   Differences from the source:
--   - encoding: a system is (V_A, V_A^+, u_A) with V_A a finite-dimensional real vector space → a system has a finite coordinate type ι with V_A = ι → ℝ, the cone a subset, and the unit a coordinate vector paired by the dot product; reason: every finite-dimensional space is ℝ^ι in a basis; (T4) refers to these fixed coordinates
--   - encoding: the identification of ℝⁿ ⊗ V_B with V_B^{⊕n} via δ_i ⊗ β ↦ (0, …, β, …, 0) → product coordinates Fin n × ι_B, block i being ξ(i, ·); the cone C_A ⊗_min C_B is written as the set of finite sums ∑_k α_k ⊗ β_k with α_k ∈ C_A, β_k ∈ C_B; reason: the same identification; a nonnegative coefficient is absorbed into α_k
--   - encoding: a classical value i occurring with probability p_i = u_B(β_i), together with the conditional state β_i/p_i of B → p_i ≥ 0 and, when p_i > 0, p_i^{-1} β_i is a state of B; reason: the probabilistic reading made explicit
--   - generalization: the standard classical n-level system Δ_n → n ranges over all natural numbers, including the zero-dimensional system Delta 0; reason: every positive dimension of the source is included; at n = 0 the tensor space and all four cones are {0}, and there are no normalized states
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.15–16 (PDF pp.17–18), Fact B.10

import Mathlib
import Definitions.Def_GPTIP632_Classical_Systems

namespace GPTIP632.Classical

/-- **Fact B.10**, pp.15–16: for the classical system `Δ_n` and any system `B`, in the product
coordinates `Fin n × ι_B` (`δ_i ⊗ β ↦` the block `i`),
`ℝⁿ_{≥0} ⊗_min V_B⁺ = ℝⁿ_{≥0} ⊗_max V_B⁺ = (V_B⁺)^{⊕n} = {∑_i δ_i ⊗ β_i : β_i ∈ V_B⁺}`; consequently
every composite of `Δ_n` with `B` has the cone `(V_B⁺)^{⊕n}`, and its states are the vectors
`∑_i δ_i ⊗ β_i` with `β_i ∈ V_B⁺` and `∑_i u_B(β_i) = 1`, where `p_i = u_B(β_i) ≥ 0` and, when
`p_i > 0`, `β_i / p_i` is a state of `B`. -/
theorem fact_B_10 (n : ℕ) (B : System) :
    minTensor (Delta n) B = maxTensor (Delta n) B ∧
    maxTensor (Delta n) B = blockCone n B ∧
    blockCone n B = {ξ | ∃ β : Fin n → B.ι → ℝ, (∀ i, β i ∈ B.cone) ∧
      ξ = ∑ i, tensorVec (Pi.single i 1 : Fin n → ℝ) (β i)} ∧
    ∀ AB : Composite (Delta n) B,
      pullCone AB.sys AB.e = blockCone n B ∧
      ∀ ω : AB.sys.ι → ℝ, (ω ∈ AB.sys.states ↔
          (∀ i, (fun j => ω (AB.e.symm (i, j))) ∈ B.cone) ∧
            ∑ i, pair B.unit (fun j => ω (AB.e.symm (i, j))) = 1) ∧
        (ω ∈ AB.sys.states → ∀ i, 0 ≤ pair B.unit (fun j => ω (AB.e.symm (i, j))) ∧
          (0 < pair B.unit (fun j => ω (AB.e.symm (i, j))) →
            (pair B.unit (fun j => ω (AB.e.symm (i, j))))⁻¹ • (fun j => ω (AB.e.symm (i, j))) ∈
              B.states)) := by sorry

end GPTIP632.Classical
