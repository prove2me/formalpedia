-- Prove2me | Theorems.Thm_OrbNetEqui_Equivariance_pointwise_equivariant
-- name    : OrbNetEqui.Equivariance.pointwise_equivariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:58.096588+00:00
-- url     : https://prove2.me/theorems/f7f15f89-5492-4610-b466-89fc22a676d4
-- title:
--   S2.6, pp. 27–28 — the point-wise interaction block (S40)–(S42) is equivariant, given the Clebsch–Gordan property (S33)
-- statement:
--   Let $(U^L)_{L\in\Lambda}$ be unitary representations of a group $K$, with finitely many labels, and let $\phi$ be the point-wise interaction block (S40)–(S42): two EvNorms (with $\beta>0$, $\epsilon>0$), two arbitrary functions $\mathrm{MLP}_1,\mathrm{MLP}_2$ of the invariant features, and coupling coefficients $C^{c,L}_{L_1;L_2}$, matrices from $\mathbb V^{L_1}\otimes\mathbb V^{L_2}$ to $\mathbb V^L$:
--   $$f_{L,c,M}=\mathrm{MLP}_1(\bar h)_{L,c}\,\hat h_{L,c,M},\quad q_{L,c,M}=g_{L,c,M}+\sum_{L_1,L_2}\sum_{M_1,M_2}f_{L_1,c,M_1}\,g_{L_2,c,M_2}\,C^{c,L,M}_{L_1M_1;L_2M_2},$$
--   $$\phi(h,g)_{L,c,M}=h_{L,c,M}+\mathrm{MLP}_2(\bar q)_{L,c}\,\hat q_{L,c,M}.$$
--
--   Let $k\in K$ satisfy the Clebsch–Gordan property (S33) in intertwining form for every $c,L_1,L_2,L$:
--   $$C^{c,L}_{L_1;L_2}\,(U^{L_1}_k\otimes U^{L_2}_k)=U^L_k\,C^{c,L}_{L_1;L_2}.$$
--   Then $\phi(k\cdot h,\ k\cdot g)=k\cdot\phi(h,g)$ for all features $h,g$.
--
--   This is the last building block in the paper's proof of G-equivariance; it is used both in the full and in the local update steps.
--
--   **Formalization Note.** (S33) is printed as $C(U^{L_1}\otimes U^{L_2})C^\dagger=U^L$; the proof uses the intertwining form above, which follows from the printed one when $C$ is a co-isometry ($CC^\dagger=1$), as Clebsch–Gordan coefficients are. The multilayer perceptrons are arbitrary functions, the EvNorm statistics are parameters, every label has the same number of channels (as (S41) requires), and the output multiplicity index $\nu(n)$ is absorbed into the channel index of $C$. The block is the S2 form (S40)–(S42), without the main text's extra channel-mixing weights $W^{\mathrm{in}},W^{\mathrm{out}}$ of (24)–(26).
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, pp. 27–28, S2.6, "Proof of G-equivariance for the point-wise interaction block (S40)-(S42)"; eqs. (S33) p. 25, (S39)–(S42) p. 26

import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic

namespace OrbNetEqui.Equivariance

open Matrix

theorem pointwise_equivariant {K : Type*} [Group K] {Λ : Type*} [Fintype Λ]
    {dim : Λ → ℕ} {nmax : ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (P : PointwiseParams Λ dim nmax) (ε : ℝ)
    (hβ : ∀ L c, 0 < P.βh L c ∧ 0 < P.βq L c) (hε : 0 < ε) (k : K)
    (hC : ∀ (c : Fin nmax) (L₁ L₂ L : Λ),
      P.C c L₁ L₂ L * Matrix.kroneckerMap (· * ·)
          (U L₁ k : Matrix (Fin (dim L₁)) (Fin (dim L₁)) ℂ)
          (U L₂ k : Matrix (Fin (dim L₂)) (Fin (dim L₂)) ℂ) =
        (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) * P.C c L₁ L₂ L)
    (h g' : Feature Λ dim nmax) :
    pointwise P ε (featAct U k h) (featAct U k g') = featAct U k (pointwise P ε h g') := by sorry

end OrbNetEqui.Equivariance
