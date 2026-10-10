-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_l1_scales
-- name    : OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_l1_scales
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:19:02.280467+00:00
-- url     : https://prove2.me/theorems/eea23bb3-6ec3-474e-bde9-8ff56f715bb6
-- title:
--   Early allocated affine radii, tolerance and layer sampler scales exist
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$ with decidable equality, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ with decidable equality indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), a finite type $\alpha$ with decidable equality, nonempty finite types $O_j$ with decidable equality, and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$ that are injective with $|\mathrm{rows}_j(o)| \le j+1$ for all $j, o$. Let $\psi : \mathbb R \to \mathbb R$ be $C^\infty$ with values in $[0,1]$, $\psi(t) = 0$ for $|t| \le 1$ and $\psi(t) = 1$ for $|t| \ge 2$; let $A, T \ge 0$ be such that $\psi$ is $A$-Lipschitz and Mathlib's `Real.smoothTransition` is $T$-Lipschitz; let $\mathrm{block}_a : O_{a.1} \to B_a$ be injective for every $a$. Let $\delta, \mathrm{target}, P_k, F, T_{\mathrm{mod}}, D$ be reals with `AllocatedComparisonDimensions B α O D` (a structure of inequalities bounding $m$, $|G|$, $|\alpha|$ and other cardinalities by $D$, with $D \ge 0$), $0 < \delta \le 1$, $\mathrm{target}, P_k, F, T_{\mathrm{mod}} \ge 0$ and $(\delta/2)^{-1} \le \exp F$. Put $\mathrm{maskLog} = D \cdot (m 2^{m+1}) \cdot P_k$, $E = \mathrm{target} + \mathrm{maskLog} + 5$, $\eta = e^{-E}$, $P_\rho = 2\,$`affineProfileInputEnvelope D A T E F` $+ 2$, $P_{\mathrm{tail}} =$ `affineProfileToleranceEnvelope m D (D(D+1) + D·D + D + 1) A T E F`, and let $K$ be the natural number chosen (by `Classical.choose`) as witness of OpenAI's existence lemma `exists_allocatedAffineScaleLog_bound m`. Then $0 \le P_\rho$, $0 \le P_{\mathrm{tail}}$, and there is a function $\rho$ from predicates on `LayerSamplerAxis I n` to nonnegative reals with $0 < \rho(P) \le 1$ and $\rho(P)^{-1} \le \exp P_\rho$ for every predicate $P$, and a real $t$ with $0 < t \le 1$ and $t^{-1} \le \exp P_{\mathrm{tail}}$, such that `AllocatedAffineCoveredComparison B rows δ η ρ t` holds (at universe levels $u_J, u_Q$; a proposition of OpenAI quantifying over subspace data, scales, cube tuples and auxiliary data) and: for all finite types $J_j$ in universe $u_J$, subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j > 0$, and every real $p \ge 0$ with $R_j^{-1} \le \exp p$ for all $j$, setting $P = p + P_{\mathrm{tail}}$, there is a `LayerSamplerScale` $S$ for $(B, U, \mathrm{basis}, R)$ with the constant width $\sigma_j = t$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities) such that $R_j^{-1} \le \exp P$ and $t^{-1} \le \exp P$ for all $j$, $\exp($`allocatedAffineLengthLog m D P Prho Pk target F Tmod`$) \le S.\mathrm{value}$, and $S.\mathrm{value} \le \exp\bigl((D + P + P_\rho + P_k + \mathrm{target} + F + T_{\mathrm{mod}} + K)^K\bigr)$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_l1_scales` in `lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineL1Scales.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B129`, `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineL1Scales.lean#L21

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B129
import Definitions.Def_OAIErdos3B136

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_l1_scales
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ target Pk F Tmod D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (htarget : 0 ≤ target) (hPk : 0 ≤ Pk) (hF : 0 ≤ F) (hTmod : 0 ≤ Tmod)
    (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {p : ℝ}, 0 ≤ p → (∀ j, (R j)⁻¹ ≤ Real.exp p) →
        let P := p + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
