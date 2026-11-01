-- Prove2me | Theorems.Thm_GaussOptCVQKD_property_ii_gaussification_invariance
-- name    : GaussOptCVQKD.property_ii_gaussification_invariance
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:02:24.51167+00:00
-- url     : https://prove2.me/theorems/c83d00b5-bf27-489a-a6ce-b7be7a3615c6
-- title:
--   Property ii) — invariance of $K_\beta$ under local Gaussification (passive orthogonal) unitaries
-- statement:
--   Fix $\beta\in[0,1]$, a reconciliation direction and the measurement choices of Alice and Bob. Then:
--
--   1. $K_\beta$ is invariant under local passive orthogonal unitaries and under relabelling: if Alice applies to her modes, and Bob to his, a passive unitary implementing a real orthogonal mixing of the modes (the same on the $x$ and on the $p$ quadratures, as the Gaussification unitary $U_G$ does), then
--   $$
--   K_\beta\bigl((U_A\otimes U_B)\,\rho\,(U_A\otimes U_B)^\dagger\bigr)=K_\beta(\rho),
--   $$
--   and $K_\beta$ does not change under an owner-preserving relabelling of the modes; both on every domain (all densities, or any energy sublevel);
--   2. for every density $\rho$ and every such pair $U_A,U_B$, the outcome mutual information, $S(\rho)$ and the averaged conditional entropies (both directions) of $(U_A\otimes U_B)\rho(U_A\otimes U_B)^\dagger$ equal those of $\rho$, in $[0,\infty]$.
--
--   Applied to $\rho_{AB}^{\otimes N}$ and $U_G\otimes U_G$ this is property ii): a passive orthogonal mixing commutes with homodyne and heterodyne detection up to an invertible linear map of the outcomes.
--
--   **Formalization Note** $K_\beta$ is not invariant under arbitrary local unitaries (a local phase rotation by $\pi/2$ turns homodyne $x$ into homodyne $p$), so the class is the passive orthogonal one, which contains $U_G$.
--
--   Differences from the source:
--
--   - generalization: U_G† ⊗ U_G† applied to ρ_AB^{⊗N} → every density and every pair of local passive unitaries implementing a real orthogonal mode mixing (the same on x and p), on every domain; reason: U_G is such a unitary ('the x and p quadratures of all N modes are thus not mixed', p.2), and ρ_AB^{⊗N} is a density
--   - generalization: a function of the bipartite state → also invariance under owner-preserving relabelling of the modes, and equality of the three pieces of K; reason: K does not depend on mode labels; the pieces are what the paper's argument ('the mutual von Neumann entropies … are invariant') compares
--   - reading: 'the mutual von Neumann entropies appearing in K(ρAB) are invariant under (any) local unitaries' → invariance of K only under the passive orthogonal class; reason: the post-measurement entropies are invariant because U_G commutes with the measurement; K itself changes under a local phase rotation, so '(any)' refers to the entropies, not to K
--   - generalization: one mode per party ((6)), or N modes per party ((7)) → every finite mode set I with every owner map I → {Alice, Bob}; reason: N = 1 or N modes on each side is the special case of an owner map with one or N modes per party
--   - generalization: direct reconciliation with perfect efficiency, K = S(a:b) − S(a:E) ((6)) → both directions (DR, and RR with a ↔ b, A ↔ B, p.3) and every reconciliation efficiency β ∈ [0, 1] (K = βS(a:b) − S(a:E), (11), p.4); reason: the paper extends its claim to RR (p.3) and to (11) (p.4) in prose; β = 1 with DR is (6)
--   - encoding: entropies and mutual information as real numbers → in nats, valued in [0, ∞] (Mathlib klDiv, published extendedEntropyNats), converted to reals in K; reason: same values where finite; the statement concludes or assumes the finiteness it needs
--   - encoding: quadratures x, p and the heterodyne outcome α → x = (a + a†)/√2, vacuum covariance I (Support50.P14); heterodyne outcome recorded as √2(Re α, Im α); outcome laws and conditional states characterized by characteristic functions; reason: Lean convention; mutual information and Holevo quantities are invariant under an invertible linear relabelling of outcomes
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Optimality of Gaussian attacks', property ii) Invariance under local Gaussification unitaries, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_GaussOptCVQKD_MeasurementModel
import Definitions.Def_GaussOptCVQKD_KeyRate
import Definitions.Def_GaussOptCVQKD_PassiveUnitary

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)
open QAlgorithms.Papers.Independent.Support50.P14 (localKernel)

namespace GaussOptCVQKD

/-- **Property ii) Invariance under local Gaussification unitaries**, García-Patrón, Cerf,
arXiv:quant-ph/0608032v1, "Optimality of Gaussian attacks", p.3: "Since the two states ρ̃_āb̄ and
ρ_ab^⊗N are related by a local unitary operation U_G† ⊗ U_G† and since the mutual von Neumann
entropies appearing in K(ρAB) are invariant under (any) local unitaries, we obtain the invariance
of K(ρAB) under local Gaussification unitaries."

For every `β ∈ [0, 1]`, direction `r` and measurement choices `mA`, `mB`:
1. `K_β` satisfies `PassiveInvariant cap` for every domain `cap`: it is unchanged when Alice and
   Bob each apply a passive unitary implementing a real orthogonal mixing of their own modes
   (the same on `x` and `p`), and under every owner-preserving relabelling of the modes;
2. for every density `ρ` and every such family of local unitaries `U`, the outcome mutual
   information, the entropy and the averaged conditional entropies (both directions) of
   `U ρ U†` equal those of `ρ` (in `[0, ∞]`).

**Formalization Note** The Gaussification operation `U_G ⊗ U_G` (Hadamard-type copy mixers at
Alice's and at Bob's side) is one such family. `K_β` is not invariant under arbitrary local
unitaries (a local phase rotation turns homodyne `x` into homodyne `p`), so the class is the
passive orthogonal one. -/
theorem property_ii_gaussification_invariance (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (r : Reconciliation) (mA mB : Measurement) :
    (∀ cap : Option ℝ, PassiveInvariant cap (keyRate β r mA mB)) ∧
    ∀ {I : Type} [Fintype I] (owner : I → Fin 2) (ρ : State (Occupation I))
      (U : (p : Fin 2) → Hilbert (Occupation {j : I // owner j = p}) ≃ₗᵢ[ℂ]
        Hilbert (Occupation {j : I // owner j = p})),
      LocalPassiveOrthogonal owner U →
      mutualInfo owner ![mA, mB] (conjugateKernel (localKernel owner U) ρ.coefficients) =
          mutualInfo owner ![mA, mB] ρ.coefficients ∧
        extendedEntropyNats (conjugateKernel (localKernel owner U) ρ.coefficients) =
          extendedEntropyNats ρ.coefficients ∧
        ∀ p q : Fin 2, p ≠ q →
          holevoIntegral owner ![mA, mB] (conjugateKernel (localKernel owner U) ρ.coefficients)
              p q =
            holevoIntegral owner ![mA, mB] ρ.coefficients p q := by sorry

end GaussOptCVQKD
