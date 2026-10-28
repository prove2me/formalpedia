-- Prove2me | Theorems.Thm_OrbNetEqui_Equivariance_blockConv_equivariant
-- name    : OrbNetEqui.Equivariance.blockConv_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:54.962288+00:00
-- url     : https://prove2.me/theorems/41628886-b5da-4693-8cc0-db2116820ba8
-- title:
--   S2.6, pp. 26–27 — the block convolution (S36) is equivariant: m_{u⃗}(g·T, g·h) = π¹(g_{u₁}) m_{u⃗}(T, h)
-- statement:
--   Let $K$ be a group with subgroups $G_u$, one per atom $u$. Let $\pi^1_u:K\to\mathrm U(\iota_u)$ be unitary representations on the atomic bases, $(U^L)_L$ unitary representations on the feature spaces, and let the matching matrices satisfy (S35):
--   $$D_u\,\pi^2_u(k)=\pi^1_u(k)\,D_u\qquad\text{for all }u\text{ and }k\in G_u,$$
--   where $\pi^2_u(k)$ acts as $U^L_k$ on each copy of $\mathbb V^L$ in $V_u$.
--
--   Then for every $g=(g_u)_u$ with $g_u\in G_u$, every N-body tensor $T$, all features $(h_u)_u$, every sub-tensor index $\vec u=(u_1,\dots,u_N)$ and every convolution channel $i$, the block convolution (S36)
--   $$(\mathbf m_{\vec u})^i_{v_1}=\sum_{v_2,\dots,v_N}T_{\vec u}(v_1,\dots,v_N)\prod_{j=2}^N\overline{\rho_{u_j}(h_{u_j})^i_{v_j}}$$
--   satisfies
--   $$\mathbf m_{\vec u}(g\cdot T,\ g\cdot h)^i=\pi^1_{u_1}(g_{u_1})\,\mathbf m_{\vec u}(T,h)^i,$$
--   where $g$ acts on $T$ by the local action (S26) and on $h_u$ by $U(g_u)$.
--
--   This is the first of the four building-block equivariances that make up the paper's proof of G-equivariance (S2.6).
--
--   **Formalization Note.** The complex conjugate in (S36) is kept: it is what makes the unitary factors cancel. The matching layer (S44) uses the main-text weight shape (16), with a multiplicity index for the copies of each $\mathbb V^L$ in $V_u$, and its weights may depend on the atom. The tensor has order $N=n+1$, and the first index is $v_1$.
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, pp. 26–27, S2.6, "Proof of G-equivariance for the convolution block (S36)"; eqs. (S26), (S35), (S36), (S44)

import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic

namespace OrbNetEqui.Equivariance

open Matrix

theorem blockConv_equivariant {K : Type*} [Group K] {d n : ℕ} {ι : Fin d → Type*}
    [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {dim : Λ → ℕ} {nmax I : ℕ} {Kmul : Fin d → Λ → ℕ}
    (S : Fin d → Subgroup K)
    (π₁ : (u : Fin d) → K →* Matrix.unitaryGroup (ι u) ℂ)
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (W : (u : Fin d) → Fin I → (L : Λ) → Matrix (Fin (Kmul u L)) (Fin nmax) ℂ)
    (hD : ∀ u, ∀ k ∈ S u, D u * π₂mat U Kmul u k = (π₁ u k : Matrix (ι u) (ι u) ℂ) * D u)
    (g : Fin d → K) (hg : ∀ u, g u ∈ S u)
    (T : (Fin (n + 1) → Orb ι) → ℂ) (h : Fin d → Feature Λ dim nmax)
    (uvec : Fin (n + 1) → Fin d) (i : Fin I) :
    blockConv D W (tensorAct π₁ g T) (fun u => featAct U (g u) (h u)) uvec i =
      (π₁ (uvec 0) (g (uvec 0)) : Matrix (ι (uvec 0)) (ι (uvec 0)) ℂ) *ᵥ
        blockConv D W T h uvec i := by sorry

end OrbNetEqui.Equivariance
