-- Prove2me | Theorems.Thm_OrbNetEqui_Equivariance_unite_equivariant
-- name    : OrbNetEqui.Equivariance.unite_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:01.06635+00:00
-- url     : https://prove2.me/theorems/9a0aaff4-a99e-4229-b94b-3eab752f5cdc
-- title:
--   S2.6, p. 26, and eq. (4), p. 3 — the UNiTE network is equivariant under local unitary changes of the atomic bases
-- statement:
--   Consider a molecule with atoms $u=1,\dots,d$, each with a finite atomic-orbital basis $\{e_{u;v}\}$, and an N-body tensor $T$ of order $N=n+1$ over the concatenated basis. Let $K$ be a group with subgroups $G_u$, let $\pi^1_u:K\to\mathrm U(\iota_u)$ be the representations on the atomic bases and $(U^L)_{L\in\Lambda}$ unitary representations on the feature spaces $\mathbb V^L$, with finitely many labels. Let $F$ be the UNiTE network (Methods 1.1): the diagonal reduction $h^0$, then $t_1$ steps of block convolution, message passing and point-wise interaction, then $t_2$ point-wise interaction steps. Assume:
--
--   1. (S35) $D_u\,\pi^2_u(k)=\pi^1_u(k)\,D_u$ for all $u$ and $k\in G_u$;
--   2. (S33) in intertwining form, $C^{t,c,L}_{L_1;L_2}(U^{L_1}_k\otimes U^{L_2}_k)=U^L_k\,C^{t,c,L}_{L_1;L_2}$, for every step $t$, every $u$ and $k\in G_u$;
--   3. (S32) for the diagonal reduction: $\psi_u\big((\pi^1_u(k))^{\otimes N}T_u\big)_{L,\nu}=U^L_k\,\psi_u(T_u)_{L,\nu}$ for all $u$ and $k\in G_u$;
--   4. invariant attention: $\alpha^t(g\cdot T,g\cdot h)=\alpha^t(T,h)$ for every step $t$ and every $g\in\prod_uG_u$;
--   5. $\beta>0$ in every EvNorm, and $\epsilon>0$.
--
--   Then for every $g=(g_u)_u$ with $g_u\in G_u$, every tensor $T$ and every atom $u$,
--   $$F(g\cdot T)_u=U(g_u)\cdot F(T)_u,$$
--   where $g\cdot T$ is the local action (S26), $(\pi^1(g_{u_1})\otimes\cdots\otimes\pi^1(g_{u_N}))T_{\vec u}$ on each sub-tensor, and $U(g_u)$ acts on every channel of label $L$ by $U^L_{g_u}$.
--
--   This is the equivariance claim (4), $R\cdot F(T[\Psi_0])\equiv F(R\cdot T[\Psi_0])$, for the local unitary basis rotations (part (a) of the group $G$ of S2.2), which the paper proves in Appendix S2.6.
--
--   **Formalization Note.** $\mathrm U(n)$ is an abstract group $K$; scalars are complex. The diagonal reduction $\psi_u$ is any linear map satisfying (S32), which includes the paper's tabulated one (Corollary S3). The multilayer perceptrons are arbitrary functions, the EvNorm statistics are fixed parameters, the attention weights at each step are an arbitrary function of the step's inputs satisfying the paper's invariance condition, and (S33) is used in intertwining form. Matching weights carry the multiplicity index of (16) and (28) and may depend on the atom and step. Permutations (b) and translations (c) of the symmetry group are not part of the statement.
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, p. 26, S2.6 G-equivariance (claim (4), p. 3; definition of G-equivariance, S2.2, p. 23)

import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic

namespace OrbNetEqui.Equivariance

open Matrix

theorem unite_equivariant {K : Type*} [Group K] {d n : ℕ} {ι : Fin d → Type*}
    [∀ u, Fintype (ι u)] [∀ u, DecidableEq (ι u)] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {dim : Λ → ℕ} {nmax I J : ℕ} {Kmul : Fin d → Λ → ℕ}
    (S : Fin d → Subgroup K)
    (π₁ : (u : Fin d) → K →* Matrix.unitaryGroup (ι u) ℂ)
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (D : (u : Fin d) → Matrix (ι u) (MIdx dim Kmul u) ℂ)
    (θ : UniteParams d n ι Λ dim nmax Kmul I J)
    (hD : ∀ u, ∀ k ∈ S u, D u * π₂mat U Kmul u k = (π₁ u k : Matrix (ι u) (ι u) ℂ) * D u)
    (hC : ∀ (t : ℕ) (u : Fin d), ∀ k ∈ S u, ∀ (c : Fin nmax) (L₁ L₂ L : Λ),
      (θ.P t).C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
          (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
          (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
        (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * (θ.P t).C c L₁ L₂ L)
    (hψ : ∀ u, ∀ k ∈ S u, ∀ (T : (Fin (n + 1) → ι u) → ℂ) (L : Λ) (ν : Fin (θ.μd u L)),
      θ.ψ u (diagAct (π₁ u k : Matrix (ι u) (ι u) ℂ) T) L ν =
        (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ θ.ψ u T L ν)
    (hα : ∀ (t : ℕ) (g : Fin d → K), (∀ u, g u ∈ S u) →
      ∀ (T : (Fin (n + 1) → Orb ι) → ℂ) (h : Fin d → Feature Λ dim nmax),
        θ.α t (tensorAct π₁ g T) (fun u => featAct U (g u) (h u)) = θ.α t T h)
    (hβ : ∀ (t : ℕ) (L : Λ) (c : Fin nmax), 0 < (θ.P t).βh L c ∧ 0 < (θ.P t).βq L c)
    (hε : 0 < θ.ε)
    (g : Fin d → K) (hg : ∀ u, g u ∈ S u) (T : (Fin (n + 1) → Orb ι) → ℂ) (u : Fin d) :
    unite θ D (tensorAct π₁ g T) u = featAct U (g u) (unite θ D T u) := by sorry

end OrbNetEqui.Equivariance
