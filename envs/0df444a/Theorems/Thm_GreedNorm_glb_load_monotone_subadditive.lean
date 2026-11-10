-- Prove2me | Theorems.Thm_GreedNorm_glb_load_monotone_subadditive
-- name    : GreedNorm.glb_load_monotone_subadditive
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:10.050252+00:00
-- url     : https://prove2.me/theorems/23abe69f-4661-418c-8cde-9b93ea8ffabc
-- title:
--   §3.3 — GLB loads $S\mapsto f_i(p_i[S])$ are monotone subadditive
-- statement:
--   GLB is an instance of Nested Cost Allocation with monotone subadditive loads. Let $v\in\mathbb R^n_{\ge0}$ and let $f$ be a monotone symmetric norm on $\mathbb R^n$. The set function $S\mapsto f(v[S])$ on subsets of the jobs satisfies
--
--   1. $f(v[S])\ge 0$ for every $S$;
--   2. $S\subseteq T\implies f(v[S])\le f(v[T])$;
--   3. $f(v[S\cup T])\le f(v[S])+f(v[T])$.
--
--   Moreover, for every GLB instance and every assignment $\sigma$, the GLB load vector of $\sigma$ equals the Nested-Cost-Allocation load vector of $\sigma$ for the loads $\mathrm{load}_i(S)=f_i(p_i[S])$:
--
--   $$
--   \bigl(f_i(p_i[\sigma])\bigr)_{i}=\bigl(\mathrm{load}_i(\sigma^{-1}(i))\bigr)_{i}.
--   $$
--
--   This is what allows the general framework of Section 3 to be applied to GLB.
--
--   Differences from the source:
--   - encoding: monotone symmetric norms on the orthant R^k_{≥0} → R_{≥0} → functions (Fin k → ℝ) → ℝ satisfying the public SymNormLoad.IsMonotoneSymmetricNorm (a norm on all of ℝ^k, monotone on the orthant); reason: every monotone symmetric norm on the orthant extends to ℝ^k by x ↦ g(|x|), and only orthant values are ever used; same instances
--   - encoding: the GLB instance of NestedCostAlloc with load_i(S) = f_i(p_i[S]) (p.2, used on p.9) → an explicit identity glbLoad p f σ = partialLoadVec (fun i S => f i (vecOn (p i) S)) (some ∘ σ); reason: states the instance correspondence the paragraph relies on; no instance changes
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.3, p.9 (PDF 11); GLB instance of NestedCostAlloc, §1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_GreedNorm_vecOn
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_GreedNorm_glbLoad
import Definitions.Def_GreedNorm_partialLoadVec

namespace GreedNorm

/-- **GLB is an instance of SubaddNestedCostAlloc.**
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.3, p.9 (PDF 11): "the load functions loadi in GLB are monotone subadditive functions of
the jobs that are assigned to machine i, and thus is an instance of SubaddNestedCostAlloc", with
the instance of §1, p.2 (PDF 4): "each load function is defined by loadi(S) = fi(pi[S])".

For a nonnegative row `v = p_i` and a monotone symmetric norm `f = f_i`, the set function
`S ↦ f(v[S])` is nonnegative, monotone and subadditive; and the GLB load vector of an
assignment `σ` is the Nested-Cost-Allocation load vector of `σ` for the loads
`load_i(S) = f_i(p_i[S])`.

**Formalization Note** Norms satisfy the public `SymNormLoad.IsMonotoneSymmetricNorm` on
`Fin n → ℝ`; subadditivity is the public `SubmodOrder.Subadditive`. -/
theorem glb_load_monotone_subadditive {n : ℕ} (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j)
    (f : (Fin n → ℝ) → ℝ) (hf : SymNormLoad.IsMonotoneSymmetricNorm f) :
    (∀ S : Finset (Fin n), 0 ≤ f (vecOn v S)) ∧
      SubsamplingSM.Offline.IsMonotoneSetFn (fun S : Finset (Fin n) => f (vecOn v S)) ∧
      SubmodOrder.Subadditive (fun S : Finset (Fin n) => f (vecOn v S)) ∧
      ∀ (m : ℕ) (p : Fin m → Fin n → ℝ) (F : Fin m → (Fin n → ℝ) → ℝ) (σ : Fin n → Fin m),
        glbLoad p F σ =
          partialLoadVec (fun i S => F i (vecOn (p i) S)) (fun j => some (σ j)) := by sorry

end GreedNorm
