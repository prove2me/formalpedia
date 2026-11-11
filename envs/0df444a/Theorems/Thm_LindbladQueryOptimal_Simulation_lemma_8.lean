-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_lemma_8
-- name    : LindbladQueryOptimal.Simulation.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:57.509371+00:00
-- url     : https://prove2.me/theorems/c3a257e7-4705-44fa-a548-d5a5b86ca156
-- title:
--   Lemma 8 — LCU error reduction for input-restricted canonical transducers
-- statement:
--   Let $V_{\rm in}:\mathcal H_{\rm in}\to\mathcal H_P$ be an isometry and let $\lambda_1,\ldots,\lambda_{s_{\max}}\in\mathbb C$ sum to one. There is an oracle-independent layerwise SELECT query program using at most $s_{\max}$ controlled applications of $S$, with known input/output isometries, that block encodes $\widetilde P=\sum_j\lambda_jP_j$ with normalization $\Lambda=\sum_j|\lambda_j|$. Restricting its source through $V_{\rm in}$ gives a block encoding of $\widetilde V=\widetilde PV_{\rm in}$ with the same normalization. For every unitary $S$, isometry $V$ and linear catalyst $\Gamma$ satisfying $S(V_{\rm in}\psi\oplus\Gamma\psi)=V\psi\oplus\Gamma\psi$ for every $\psi$, the exact error identity is
--   $$V-\widetilde V=S_{P\leftarrow C}\,p_{\rm err}(S_{C\leftarrow C})\,\Gamma.$$
--   Here every $P_j$ is computed from the actual Fourier/shared-private reuse circuit, and $p_{\rm err}=\sum_j\lambda_jg_j$. The program and its layouts are chosen before $S$; its unitary and block-encoding properties are conclusions.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert operators and direct sums → complex matrices indexed by finite types and sum types; reason: coordinate representation preserves every source instance and the spectral norm
--   - encoding: coefficients indexed from 1 through s_max and positive reuse lengths → Fin s_max coefficients with reuse length j.val+1 and an explicit positive s_max; reason: the same finite family; the sum-one hypothesis also excludes an empty family
--   - encoding: a block encoding using s_max controlled applications of S → a finite SELECT program with an independent count at most s_max and known isometric input/output embeddings; reason: expresses the stated query upper bound and its source restriction without assuming the compiled block
--   - generalization: S has the canonical factorization S°(I⊕O) as well as the restoration identity → any unitary S with the input-restricted restoration identity; reason: the reuse/LCU argument uses S as its query primitive; every canonical source transducer is included
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Lemma 8, pp. 11–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Reuse

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_8 (i p c s : ℕ) (hs : 0 < s)
    (Vin : Matrix (Fin p) (Fin i) ℂ) (hVin : Vinᴴ * Vin = 1)
    (lam : Fin s → ℂ) (hlam : ∑ j, lam j = 1) :
    ∃ (w : ℕ) (gates : List (ReuseGate w (p+c)))
      (Bin Bout : Matrix (Fin w) (Fin p) ℂ),
      Binᴴ * Bin = 1 ∧ Boutᴴ * Bout = 1 ∧ reuseQueryCount gates ≤ s ∧
      ∀ (S : Op (Sum (Fin p) (Fin c))) (hS : unitary S)
        (V : Matrix (Fin p) (Fin i) ℂ) (Γ : Matrix (Fin c) (Fin i) ℂ),
        Vᴴ * V = 1 →
        S * Matrix.fromRows Vin Γ = Matrix.fromRows V Γ →
        let P := lcuReuse lam S
        let Λ := lcuNormalization lam
        let U := reuseProgramMatrix gates (numberedTransducer S)
        let SPC : Matrix (Fin p) (Fin c) ℂ := fun x y => S (.inl x) (.inr y)
        let SCC : Op (Fin c) := fun x y => S (.inr x) (.inr y)
        0 < Λ ∧ unitary U ∧ Boutᴴ * U * Bin = (Λ : ℂ)⁻¹ • P ∧
        (Bin * Vin)ᴴ * (Bin * Vin) = 1 ∧
        Boutᴴ * U * (Bin * Vin) = (Λ : ℂ)⁻¹ • (P * Vin) ∧
        V - P * Vin = SPC * reuseErrorPolynomial lam SCC * Γ := by sorry

end LindbladQueryOptimal.Simulation
