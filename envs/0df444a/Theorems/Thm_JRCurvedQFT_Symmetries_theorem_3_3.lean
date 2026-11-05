-- Prove2me | Theorems.Thm_JRCurvedQFT_Symmetries_theorem_3_3
-- name    : JRCurvedQFT.Symmetries.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T07:02:57.425326+00:00
-- url     : https://prove2.me/theorems/4e155e0c-f897-4e98-94c3-03a1a6935e90
-- title:
--   Theorem 3.3 (Quantization I)
-- statement:
--   Let $\mathcal E$ be a complex Hilbert space with reflection data: a closed subspace $\mathcal E_+$ and a unitary involution $\Theta$ with $\operatorname{Re}\langle\Theta x,x\rangle\ge0$ on $\mathcal E_+$. Let $\mathcal H$ be the completion of $\mathcal E_+/\mathcal N$, with quantization map $\Pi$. If the operator $T$ on $\mathcal E$ satisfies QC-I with subdomain $\mathscr D_0$, then
--
--   1. $T\restriction\mathscr D_0$ and $T^+\restriction\mathscr D_0$ have quantizations $\hat T$ and $\widehat{T^+}$ with domain $\hat{\mathscr D}_0$;
--   2. $\hat T^*$ and $\widehat{T^+}$ agree on $\hat{\mathscr D}_0$;
--   3. $\hat T\restriction\hat{\mathscr D}_0$ has a closure, namely $\hat T^{**}$.
--
--   This is the basic criterion by which an operator on the Euclidean space $\mathcal E$ descends to the quantum Hilbert space.
--
--   Differences from the source:
--   - generalization: E = L²(S′, µ), Θ = Γ(θ) and E₊ = E_{Ω₊} → any complex Hilbert space with reflection data; reason: the proof uses only that Θ is a unitary involution and the form is positive on the closed subspace E₊; the paper's setting is an instance
--   - encoding: "there is a subdomain D₀" in QC-I → D₀ is a parameter of SatisfiesQCI; reason: the conclusions name D₀, so it is fixed by the hypothesis
--   - encoding: (3.1): ∫ conj(Γ(θ)F) F dµ ≥ 0, i.e. (F, F) = ⟨ΘF, F⟩ ≥ 0 → 0 ≤ Re⟪ΘF, F⟫ on E₊, in ReflectionData.positive; reason: ⟪ΘF, F⟫ is real since Θ is a self-adjoint unitary, so the real part loses nothing; Reading 6
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Theorem 3.3, p. 4; Definition 3.2, p. 4

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_plusOp
import Definitions.Def_JRCurvedQFT_Symmetries_IsQuantization
import Definitions.Def_JRCurvedQFT_Symmetries_SatisfiesQCI
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace JRCurvedQFT.Symmetries

/-- **Theorem 3.3 (Quantization I).** If `T` satisfies QC-I with subdomain `D₀`, then `T↾D₀` and `T⁺↾D₀` have
quantizations `T̂` and `T̂⁺` with domain `D̂₀`; `T̂*` and `T̂⁺` agree on `D̂₀`; and `T̂↾D̂₀` has a closure,
namely `T̂**`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Theorem 3.3, p. 4.

**Formalization Note** (ii) is `T̂⁺ ≤ T̂*` in the extension order of partial operators (`D̂₀ ⊂ D(T̂*)` and
`T̂* = T̂⁺` on `D̂₀`), as (3.6), p. 5, shows. The theorem is stated for any reflection data on any complex
Hilbert space `E`; the paper's `E` and `Θ` are one instance. -/
theorem theorem_3_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (r : ReflectionData E) (T : E →ₗ.[ℂ] E) (D0 : Submodule ℂ E) (h : SatisfiesQCI r T D0) :
    ∃ That Tplus : OS r →ₗ.[ℂ] OS r,
      IsQuantization r T D0 That ∧ IsQuantization r (plusOp r T) D0 Tplus ∧
      Tplus ≤ That.adjoint ∧
      That.IsClosable ∧ That.closure = That.adjoint.adjoint := by sorry

end JRCurvedQFT.Symmetries
