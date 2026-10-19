-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedSourceNumerics_shared_width_canonical_spatial_size_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_size_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:36:02.783144+00:00
-- url     : https://prove2.me/theorems/01f2408f-9e74-4355-bdde-efa93627b44e
-- title:
--   Under allocated source numerics, a large spatial side makes the shared-width canonical spatial resolution fit in ξτN
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $b_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$, $S$ a `LayerSamplerScale B U b R σ` (defined by OpenAI, with positive natural number `S.value`), and $C, V : \mathrm{Fin}\ m \to \mathbb{R}_{\ge 0}$.
--
--   **Hypotheses.** Let $P$ be real and suppose `AllocatedSourceNumerics B U b S C V P` holds (a structure of numerical bounds defined by OpenAI: $0 \le P$, $m \le P$, the number of variables is at most $P$, `S.value` $\le e^{P}$, $R_j^{-1}, \sigma_j^{-1}, C_j, V_j \le e^{P}$, various cardinalities at most $P$, and similar). Suppose $R_j > 0$ and $\sigma_j > 0$ for all $j$. Let $X$ be a finite type, $\mathrm{dim}, M$ natural numbers, `selection` an embedding $\mathrm{Fin}\ \mathrm{dim} \hookrightarrow G$, and $p, \mathrm{target}, E_{\mathrm{cap}}, Q_{\mathrm{stride}}, E_{\tau}, \xi, B_{\xi}$ real numbers with $p \ge 0$, $\mathrm{target} \ge 0$, $E_{\mathrm{cap}} \ge 0$, $Q_{\mathrm{stride}} \ge 0$, $E_{\tau} \ge 0$, $M > 0$, $m + 1 \le p$, $\mathrm{dim} + 1 \le p$, $|G| \le p$, $|X| \le p$, $M \le e^{p}$, $\xi > 0$ and $\xi^{-1} \le e^{B_{\xi}}$. Let $\mathrm{stride}, N : X \to \mathbb{N}$ with $\mathrm{stride}(i) \le e^{Q_{\mathrm{stride}}}$ for all $i$, and let $\tau > 0$ with $\tau^{-1} \le e^{E_{\tau}}$. Suppose that for every $i \in X$,
--   $$\exp\bigl(\texttt{sharedWidthNormalizedTupleSideLog}\ X\ K\ \mathrm{selection}\ p\ \mathrm{target}\ \ell\ B_{\xi}\bigr) \le N(i),$$
--   where $K$ = `PrincipalTupleIndex B (layerSamplerDegree I n)`, $\ell$ = `allocatedSpatialLateLog B P P` $+ E_{\mathrm{cap}} + Q_{\mathrm{stride}} + E_{\tau}$, and `sharedWidthNormalizedTupleSideLog` and `allocatedSpatialLateLog` are explicit real-valued functions defined by OpenAI.
--
--   **Conclusion.** Let $W$ = `allocatedPhysicalRootBudget B U b S (fun _ => 0)` (which equals the number of elements of `LayerSamplerVariables G I n B` times `S.value`), $C_0 = 1 + \texttt{S.value} + W$, and $C_{\mathrm{entry}}$ = `allocatedPhysicalEntryBudget B U b S (fun _ => 0)` $= 1 + W + \texttt{S.value}$. Then for every $i \in X$,
--   $$8\,(1 + W)\,\mathrm{stride}(i)\cdot \texttt{normalizedTupleResolution}\ X\ K\ \mathrm{selection}\ M\ p\ \mathrm{target}\ C_0\ W\ e^{E_{\mathrm{cap}}}\ C_{\mathrm{entry}} \le (\xi\tau)\, N(i),$$
--   where `normalizedTupleResolution` is an explicit real-valued function defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_size_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_size` (in `lean/OAI/Combinatorics/Progressions/Geometry/SharedWidthAllocatedCanonicalSpatialNativeSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B125`, `OAIE3v2B126`, `OAIE3v2B180` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/SharedWidthAllocatedCanonicalSpatialNativeSource.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedSourceNumerics.shared_width_canonical_spatial_size)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B125
import Definitions.Def_OAIE3v2B126
import Definitions.Def_OAIE3v2B180

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

theorem AllocatedSourceNumerics.shared_width_canonical_spatial_size_s2
    {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {X : Type*} [Fintype X] {dim M : ℕ} (selection : Fin dim ↪ G)
    {p target Ecap Qstride Etau ξ Bξ : ℝ}
    (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hEcap : 0 ≤ Ecap) (hQstride : 0 ≤ Qstride) (hEtau : 0 ≤ Etau)
    (hM : 0 < M) (hm : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hξ : 0 < ξ) (hξB : ξ⁻¹ ≤ Real.exp Bξ)
    (stride N : X → ℕ) (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    {τ : ℝ} (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Etau)
    (hside : ∀ i, Real.exp (sharedWidthNormalizedTupleSideLog X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p target
      (allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau) Bξ) ≤ (N i : ℝ)) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let C₀ := 1 + (S.value : ℝ) + W
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    ∀ i, 8 * (1 + W) * (stride i : ℝ) * normalizedTupleResolution X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target
      C₀ W (Real.exp Ecap) Centry ≤
        (ξ * τ) * (N i : ℝ) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
