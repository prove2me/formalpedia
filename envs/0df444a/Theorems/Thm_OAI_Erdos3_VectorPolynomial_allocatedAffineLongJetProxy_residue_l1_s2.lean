-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLongJetProxy_residue_l1_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_l1_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:22:21.822576+00:00
-- url     : https://prove2.me/theorems/c6be12cd-9a71-4953-b890-519b52720149
-- title:
--   The residue-conditioned average of the allocated long-jet density is L1-close to the affine long-jet proxy
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type with decidable equality; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types with decidable equality indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $\mathrm{basis}_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$. Let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (a structure defined by OpenAI, with a natural-number value `S.value` and a positivity proof `S.positive`). Let $\alpha$ be a finite type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value`, and $u$ an element of `PrincipalAxisTuples` for the axes not in the grid set `allocatedGridAxis U basis S.value`, with sides `allocatedPrincipalSides B U basis S` (all defined by OpenAI). Let $O_j$ be finite types with decidable equality, $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$, and $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` embeddings such that, for every $j$, the square submatrix (columns selected by $s_j$) of the integer jet matrix `scalarKernelIntegerJet x (j+1) (rows j)` has nonzero determinant (call this hypothesis $h_A$). Let $M_k$ be a positive natural number and assume `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (h_A j) (1/M_k)` for every $j$ (defined by OpenAI: the operator norm of the inverse of the fixed pivot map is at most an explicit allowance). Let $P \ge 0$ be real with $M_k \le e^{P}$, and for every $j$: $R_j \le e^{P}$, $R_j^{-1} \le e^{P}$, $\sigma_j^{-1} \le e^{P}$, and $|\texttt{BoundedCoefficientExponent}\ K\ (j+1)| + 1 \le e^{P}$, where $K$ = `LayerSamplerVariables G I n B`.
--
--   Write `Tuple` for the index type `PrincipalTupleIndex` $= \Sigma_a\, B_a \times \mathrm{Fin}(\deg a)$ over the non-grid axes $a$ (with $\deg$ = `layerSamplerDegree I n`), `Jet` for $\Sigma_a O_{a.1}$ over the non-grid axes, $\beta = \exp(\texttt{allocatedDensityLog}\ B\ \alpha\ O\ P)$, $\mathrm{cap} = \beta^{|\texttt{LayerSamplerAxis I n}|}$ and $\mathrm{lip} = |\texttt{LayerSamplerAxis I n}| \cdot \beta \cdot \mathrm{cap}$.
--
--   **Hypotheses.** Assume $\sigma_j \le 1$ for all $j$. Let $L, \mathrm{step}, H, M : \mathrm{Tuple} \to \mathbb{N}$ and $c : \mathrm{Tuple} \to \mathbb{Z}$ with, for every $t \in \mathrm{Tuple}$: $L_t > 0$, $\mathrm{step}_t > 0$, $H_t \ge 2$. Let $\delta > 0$ and assume, for every $t$, that the progression $\{c_t + \mathrm{step}_t \cdot k : 0 \le k < H_t\}$ (`integerProgressionSupport`) is contained in $[0, L_t)$ and has at least $\delta L_t$ elements. Let $\mathrm{modulus} : \mathrm{Tuple} \to \mathrm{Option}\,\alpha \to \mathbb{N}$ and residues $\mathrm{residue}_{t,i} \in \mathbb{Z}/\mathrm{modulus}_{t,i}$ with $0 < \mathrm{modulus}_{t,i} \le M_t$ for all $t, i$, and assume for every $t$: $(|\alpha| + 1) M_t \le H_t$ and
--   $$\texttt{scalarCubeGridBoundaryConstant}\ \alpha \cdot \frac{M_t}{H_t} < \operatorname{vol}(\texttt{scalarCubeDomain}\ \alpha),$$
--   where `scalarCubeGridBoundaryConstant α` $= 2^{|\alpha|+1} \cdot 4^{|\alpha|} \cdot 2 \cdot (|\alpha| + 1)$ (the first factor is $|\mathrm{Bool} \times \mathrm{Finset}\,\alpha|$) and `scalarCubeDomain α` is the open scalar cube domain in $\mathbb{R}^{\mathrm{Option}\,\alpha}$ (both defined by OpenAI). Let $\varepsilon \ge 0$ with $\mathrm{step}_t / L_t \le \varepsilon$ for all $t$.
--
--   **Conclusion.** For $z : \mathrm{Jet} \to \mathbb{R}$ define
--   $$\Delta(z) = \mathbb{E}_{v}\Bigl[\texttt{allocatedNormalizedLongJetDensity}\ \ldots\ \bigl(y(v)\bigr)\ z\Bigr] - \texttt{allocatedAffineLongJetProxy}\ \ldots\ (\mathrm{center})\ (\mathrm{width})\ z,$$
--   where:
--   - the expectation is over $v = (v_t)_{t}$ drawn from the product over $t \in \mathrm{Tuple}$ of the laws `scalarCubeResidueWeights α (H t) (M t) … (modulus t) (residue t) …` (defined by OpenAI: the uniform law on the integer points $v_t \in [-H_t, H_t)^{\mathrm{Option}\,\alpha}$ all of whose cube values $v_{t,\mathrm{none}} + \sum_{i \in s} v_{t,\mathrm{some}\,i}$ ($s \subseteq \alpha$) lie in $[0, H_t)$, conditioned on the residue classes $v_{t,i} \equiv \mathrm{residue}_{t,i} \pmod{\mathrm{modulus}_{t,i}}$);
--   - $y(v)$ is the flattening (`principalTupleFlatten`) of $(t, i) \mapsto \bigl([i = \mathrm{none}]\, c_t + \mathrm{step}_t\, v_{t,i}\bigr) / L_t$;
--   - `allocatedNormalizedLongJetDensity B U basis S x u rows s h_A` and `allocatedAffineLongJetProxy B U basis S x u rows s h_A` are densities on $\mathbb{R}^{\mathrm{Jet}}$ defined by OpenAI (the latter is the mixture over a Boolean source of an affine long-jet density with the given center and width);
--   - $\mathrm{center}$ = `principalProgressionSliceCenter L c`, the flattening of $(t, i) \mapsto [i = \mathrm{none}]\, c_t / L_t$, and $\mathrm{width}$ = `principalProgressionSliceWidth L H step`, the flattening of $(t, i) \mapsto \mathrm{step}_t (H_t - 1) / L_t$.
--
--   Then $\Delta$ is Lebesgue integrable on $\mathbb{R}^{\mathrm{Jet}}$ and
--   $$\int |\Delta(z)|\, dz \le \Bigl( \Bigl( \frac{2\,\mathrm{cap} \cdot \texttt{scalarCubeGridBoundaryConstant}\ \alpha}{\operatorname{vol}(\texttt{scalarCubeDomain}\ \alpha)} + 2\,\mathrm{lip} \Bigr) \sum_{t \in \mathrm{Tuple}} \frac{M_t}{H_t} + \mathrm{lip} \cdot \varepsilon \Bigr) \cdot \bigl(2 \exp(\texttt{allocatedJetSupportLog}\ B\ \alpha\ O\ P)\bigr)^{|\mathrm{Jet}|},$$
--   where `allocatedDensityLog` and `allocatedJetSupportLog` are explicit real-valued functions defined by OpenAI, the second equal to `allocatedDensityLog B α O P` $+ P + \sum_j \bigl(|\texttt{BoundedCoefficientExponent}\ K\ (j+1)| + |\alpha|\,(j + 2)\bigr)$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_l1_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_l1` (in `lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineResidueSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/EarlyAllocatedAffineResidueSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_residue_l1)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B α O P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedAffineLongJetProxy_residue_l1_s2 (hσ1 : ∀ j, σ j ≤ 1)
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε) :
    let Δ := fun z : Jet → ℝ => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) α
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z) -
      allocatedAffineLongJetProxy B U basis S x u rows s hA
        (principalProgressionSliceCenter (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L c)
        (principalProgressionSliceWidth (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L H step) z
    Integrable Δ ∧ (∫ z, |Δ z|) ≤
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Jet := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
