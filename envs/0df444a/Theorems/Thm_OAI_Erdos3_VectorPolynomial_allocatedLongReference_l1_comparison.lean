-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongReference_l1_comparison
-- name    : OAI.Erdos3.VectorPolynomial.allocatedLongReference_l1_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:35:06.767968+00:00
-- url     : https://prove2.me/theorems/b1d9a735-eb03-474c-8b44-f3a8e776d90c
-- title:
--   Long profile densities of two Lipschitz test functions are L1-close
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $O_j$ be finite types, $\alpha$ a type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$, $\mathrm{modulus} \in \mathbb N$, and matrices $\mathrm{residue}_j$ over $\mathbb Z/\mathrm{modulus}$ indexed by $O_j \times$ `AllocatedNonkernelCoefficient B j`. Let grid be `allocatedGridAxis U b S.value` (a predicate on `LayerSamplerAxis I n`), let output be the finite type $\Sigma_{a : \{a \mid \neg\,\mathrm{grid}\,a\}}\, O_{a.1}$, let integerOutput be its subtype cut out by `allocatedLongIntegerCoordinate B U b S` (the entries whose axis is of the $\mathrm{Fin}(n_j)$ kind), and let realOutput be the complement of the range of `allocatedLongIntegerSelect B U b S` (the inclusion of integerOutput into output). Write $\mu$ for the measure `allocatedLongJetReference B U b S O` and $D_f$ for `allocatedLongProfileDensity B U b S x rows modulus residue f`. Let $f, g : \mathbb R^{\mathrm{output}} \to \mathbb R$, let $K_f, K_g, R_o \ge 0$, and assume: $f$ is $K_f$-Lipschitz and $g$ is $K_g$-Lipschitz (for the sup norm); $f(v) = 0$ and $g(v) = 0$ whenever $\|v\| > R_o$; reals $C_f, C_g \ge 0$ with $|f(v)| \le C_f$ and $|g(v)| \le C_g$ for all $v$; $f - g$ is Lebesgue integrable; and, for a real $\varepsilon$, $\int |f - g| \le \varepsilon$. Let mesh and $C$ be reals with $0 \le \mathrm{mesh} \le 1$, $1/S.\mathrm{value}^{\,t+1} \le \mathrm{mesh}$ where $t =$ `layerTailDegree m` $= m(2^{m+1}+1)$, and $1 \le C$, and assume that for all $j$ and all $z \in \mathbb Z^{O_j}$, $0 \le$ `allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z` $\le C$. Then
--   $$\int |D_f(z) - D_g(z)|\,d\mu(z) \le C^{|\texttt{LayerSamplerAxis I n}|}\Bigl(\varepsilon + (2R_o)^{|\mathrm{realOutput}|}\bigl((2R_o+2)^{|\mathrm{integerOutput}|}(K_f + K_g)\,\mathrm{mesh}\bigr)\Bigr).$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedLongReference_l1_comparison` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedActualHaarComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B176` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedActualHaarComparison.lean#L33

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B176

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U b S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U b S (O := O))
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => allocatedLongProfileDensity B U b S x rows modulus residue

theorem allocatedLongReference_l1_comparison
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hfb : ∀ v, |f v| ≤ Cf) (hgb : ∀ v, |g v| ≤ Cg)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh C : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C) :
    (∫ z, |density f z - density g z| ∂reference) ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
