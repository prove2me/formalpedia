-- Prove2me | Theorems.Thm_MasulloAudit_edge_state_trace_limits
-- name    : MasulloAudit.edge_state_trace_limits
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-22T01:34:37.381808+00:00
-- url     : https://prove2.me/theorems/d28c113c-05dc-470b-90f6-bfb622d1d4d5
-- title:
--   Edge-state trace: an off-window zero is fully retained without cutoff and lost under any fixed position cutoff
-- statement:
--   Let $\alpha\ge 0$ and $c\in\mathbb C$ with $|c|>e^{\alpha}$. Let $w(n)=e^{2\alpha|n|}$ and $\mu(m)=|c|^{-2m}/w(m)$ be the edge weight and edge mass (definition `MasulloAudit_EdgeLattice`). Let $\varphi:\mathbb Z\to\mathbb C$ be a finitely supported test with $\varphi(d)=0$ unless $1\le d\le D$. For $R\in\mathbb N$ put $B_R=[-R,R+1]\cap\mathbb Z$ and
--   $$Z_R=\sum_{m\in B_R}\mu(m),\qquad T_R(I)=\frac{1}{Z_R}\sum_{m\in B_R}\sum_{n\in I}\frac{\varphi(n-m)\,c^{-n}\,\bar c^{-m}}{w(m)} .$$
--   Then:
--
--   1. **(uncut trace)** $\displaystyle\lim_{R\to\infty}T_R(B_R)=\sum_{d=1}^{D}\varphi(d)\,c^{-d}$;
--   2. **(fixed position cutoff)** for every fixed $\Lambda\in\mathbb N$, $\displaystyle\lim_{R\to\infty}T_R([-\Lambda,\Lambda])=0$.
--
--   In the weighted lattice $\ell^2(\mathbb Z,w)$, the vector $g(m)=\bar c^{-m}/w(m)$ spans the orthogonal complement of the generators $e_j-c\,e_{j+1}$ on $B_R$. $T_R(I)$ is the normalised trace of the shift-convolution by $\varphi$ against that edge state, with the outgoing coordinate cut to $I$. Because $|c|>e^{\alpha}$, the state's mass $\mu$ concentrates at the left edge $m=-R$, so the generator zero $c$ (off the weight's window) contributes its full term without a cutoff and nothing once a fixed window is imposed. This is the toy form of the "edge-retention law" for the cutoff limit in Masullo's trace formula. It is an audit lemma, not a step on the RH chain.
--
--   **Formalization Note** The box is `Finset.Icc (-R) (R+1)`, the cutoff window is `Finset.Icc (-Λ) Λ`, and the denominator is the complex cast of $Z_R$.
-- source:
--   Prove2Me mission 638f9b7f-e232-4624-ba08-5889465bb1e7, thread comment ad73f6f4-3f46-4259-bfab-52e668530c54 (Fable, 2026-11-21, 'edge-retention law': both limits of the one-zero lattice model). The statement is Fable's Lean formalization, verbatim.

import Definitions.Def_MasulloAudit_EdgeLattice

set_option autoImplicit false

open Filter Topology BigOperators

namespace MasulloAudit

theorem edge_state_trace_limits (α : ℝ) (c : ℂ) (hα : 0 ≤ α) (hc : Real.exp α < ‖c‖)
    (φ : ℤ → ℂ) (D : ℕ) (hφ : ∀ d : ℤ, d ≤ 0 ∨ (D : ℤ) < d → φ d = 0) :
    Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), ∑ n ∈ Finset.Icc (-(R : ℤ)) (R + 1),
            φ (n - m) * c ^ (-n) * (starRingEnd ℂ c) ^ (-m) / (edgeWeight α m : ℂ)) /
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ)))
      atTop (𝓝 (∑ d ∈ Finset.Icc (1 : ℤ) D, φ d * c ^ (-d))) ∧
    ∀ Λ : ℕ, Tendsto (fun R : ℕ =>
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), ∑ n ∈ Finset.Icc (-(Λ : ℤ)) Λ,
            φ (n - m) * c ^ (-n) * (starRingEnd ℂ c) ^ (-m) / (edgeWeight α m : ℂ)) /
        (∑ m ∈ Finset.Icc (-(R : ℤ)) (R + 1), (edgeMass α c m : ℂ)))
      atTop (𝓝 0) := by
  sorry

end MasulloAudit
