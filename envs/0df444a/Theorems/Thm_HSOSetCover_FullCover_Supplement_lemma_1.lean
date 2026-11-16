-- Prove2me | Theorems.Thm_HSOSetCover_FullCover_Supplement_lemma_1
-- name    : HSOSetCover.FullCover.Supplement.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:15:39.571641+00:00
-- url     : https://prove2.me/theorems/9dfcabaa-086c-4109-8077-10dcf2c63517
-- title:
--   Lemma 1 — successively locally dual-certified partial covers form a certified $\rho$-cover
-- statement:
--   Fix a WSC instance, a target $\rho\ge1$, and a feasible dual vector $y$. Suppose the PTM successively retains partial covers $P_1,\dots,P_H$. Suppose that, for each $h$, $P_h$ satisfies the local dual-certification condition for
--   $$R_{h-1}=U\setminus\bigcup_{\ell<h}\bigcup_{j\in P_\ell}S_j .$$
--   If the sets indexed by $C=\bigcup_{h=1}^HP_h$ cover $U$, then $C$ is a certified $\rho$-cover, and
--   $$w(C)\le\rho L\le\rho\,\mathrm{OPT}.$$
--
--   This primal-dual charging argument certifies the covers assembled from partial responses in Theorems 4 and 5.
--
--   Differences from the source:
--   - encoding: candidate indices [m] and partial covers P_1, …, P_H → an arbitrary finite index type and a sequence P_0, …, P_{H−1}; reason: relabelling only
-- source:
--   Jie Wang, Computing Weighted Set Covers with Heterogeneous Stochastic Oracles: Deadline-Constrained Token Complexity, STOC 2027 submission #191 (October 2026), SHA-256 d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf, Lemma 1, PDF p. 9 / printed p. 8; proof Appendix A.3, PDF p. 15 / printed p. 14

import Mathlib
import Definitions.Def_HSOSetCover_FullCover_Supplement_WSC

namespace HSOSetCover.FullCover.Supplement

/-- **Lemma 1**, PDF p. 9 / printed p. 8 (proof Appendix A.3, PDF p. 15). Fix `ρ ≥ 1` and a
feasible dual vector `y`. If partial covers `P_0, …, P_{H-1}` are retained successively and each
`P_h` satisfies the local dual-certification condition for the residual
`R_{h-1} = U ∖ ⋃_{ℓ < h} ⋃_{j ∈ P_ℓ} S_j`, and the sets indexed by `C = ⋃_h P_h` cover `U`, then
`C` is a certified `ρ`-cover and `w(C) ≤ ρ L ≤ ρ OPT`. -/
theorem lemma_1 {U ι : Type*} [Fintype U] [DecidableEq U] [Fintype ι] [DecidableEq ι]
    (W : WSCInstance U ι) (ρ : ℝ) (hρ : 1 ≤ ρ) (y : U → ℝ) (hy : W.DualFeasible y)
    (Ps : ℕ → Finset ι) (H : ℕ)
    (hcert : ∀ h < H, W.LocalDualCert ρ y (Ps h) (W.residual (prefixUnion Ps h)))
    (hcover : W.IsCover (prefixUnion Ps H)) :
    W.CertifiedCover ρ (prefixUnion Ps H) ∧
      W.weight (prefixUnion Ps H) ≤ ρ * W.lpValue ∧ ρ * W.lpValue ≤ ρ * W.opt := by sorry

end HSOSetCover.FullCover.Supplement
