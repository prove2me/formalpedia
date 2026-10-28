-- Prove2me | Theorems.Thm_OrbNetEqui_Equivariance_messagePassing_equivariant
-- name    : OrbNetEqui.Equivariance.messagePassing_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:49.920862+00:00
-- url     : https://prove2.me/theorems/5c0d033e-210a-4d68-8e79-5de856d4dd1e
-- title:
--   S2.6, p. 27 — message passing (S37)–(S38) is equivariant: m̃_{u₁} ↦ π¹(g_{u₁}) m̃_{u₁}, and ρ†_{u₁}(m̃) ↦ U(g_{u₁}) ρ†_{u₁}(m̃)
-- statement:
--   Assume the setting of the block-convolution milestone: subgroups $G_u$ of a group $K$, unitary representations $\pi^1_u$ and $U^L$, and matching matrices satisfying (S35) $D_u\pi^2_u(k)=\pi^1_u(k)D_u$ for $k\in G_u$. Fix scalar attention weights $\alpha^j_{\vec u}$; using the same $\alpha$ before and after the transformation expresses the paper's invariance condition $g\cdot\alpha=\alpha$.
--
--   For $g=(g_u)_u$ with $g_u\in G_u$, any tensor $T$, features $h$ and atom $u_1$, the aggregated message (S37)
--   $$\tilde{\mathbf m}_{u_1}=\sum_{u_2,\dots,u_N}\bigoplus_{i,j}(\mathbf m_{\vec u})^i\,\alpha^j_{\vec u}$$
--   satisfies:
--
--   1. $\tilde{\mathbf m}_{u_1}(g\cdot T,g\cdot h)^{(i,j)}=\pi^1_{u_1}(g_{u_1})\,\tilde{\mathbf m}_{u_1}(T,h)^{(i,j)}$ for every $(i,j)$;
--   2. the reverse matching layer (S45) turns it into an equivariant feature: $\rho^\dagger_{u_1}\big(\tilde{\mathbf m}_{u_1}(g\cdot T,g\cdot h)\big)=g_{u_1}\cdot\rho^\dagger_{u_1}\big(\tilde{\mathbf m}_{u_1}(T,h)\big)$.
--
--   Together these give the equivariance of the second argument of the update (S38).
--
--   **Formalization Note.** The page displays only the first conclusion. The second one, about the reverse matching layer (S45), is the step that (S38) also needs, and it is added to complete the page's claim for "(S37)-(S38)". The reverse matching weights have the main-text shape (28), $W^\dagger_L\in\mathbb C^{n_{\max}\times K_L I J}$, and may depend on the atom.
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, p. 27, S2.6, "Proof of G-equivariance for the message passing block (S37)-(S38)"; eqs. (S37), (S38), (S45)

import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic

namespace OrbNetEqui.Equivariance

open Matrix

theorem messagePassing_equivariant {K : Type*} [Group K] {d n : ℕ} {ι : Fin d → Type*}
    [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {dim : Λ → ℕ} {nmax I J : ℕ} {Kmul : Fin d → Λ → ℕ}
    (S : Fin d → Subgroup K)
    (π₁ : (u : Fin d) → K →* Matrix.unitaryGroup (ι u) ℂ)
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (Wd : (u : Fin d) → (L : Λ) → Matrix (Fin nmax) (Fin (Kmul u L) × Fin I × Fin J) ℂ)
    (hD : ∀ u, ∀ k ∈ S u, D u * π₂mat U Kmul u k = (π₁ u k : Matrix (ι u) (ι u) ℂ) * D u)
    (g : Fin d → K) (hg : ∀ u, g u ∈ S u)
    (T : (Fin (n + 1) → Orb ι) → ℂ) (h : Fin d → Feature Λ dim nmax)
    (α : (Fin (n + 1) → Fin d) → Fin J → ℂ) (u : Fin d) :
    aggregate D W (tensorAct π₁ g T) (fun w => featAct U (g w) (h w)) α u =
        (fun ij => (π₁ u (g u) : Matrix (ι u) (ι u) ℂ) *ᵥ aggregate D W T h α u ij) ∧
      revMatching D Wd u (aggregate D W (tensorAct π₁ g T) (fun w => featAct U (g w) (h w)) α u) =
        featAct U (g u) (revMatching D Wd u (aggregate D W T h α u)) := by sorry

end OrbNetEqui.Equivariance
