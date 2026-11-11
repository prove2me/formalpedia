-- Prove2me | Theorems.Thm_LooseHamHitting_Main_claim_4_4
-- name    : LooseHamHitting.Main.claim_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:18:45.281271+00:00
-- url     : https://prove2.me/theorems/4bb1e3e4-b0b9-47a4-9ce5-03a6a0d665ad
-- title:
--   Claim 4.4 — conditional on the exposure (m, B, T), H_{τ1} − B is uniform with the prescribed degree lower bounds
-- statement:
--   Let $n$ be even and sufficiently large. In the random 3-uniform hypergraph process on $[n]$, reveal $\tau_1=m$, the set $B$ of vertices of degree at most $d_0=\lfloor0.01\log n\rfloor$ in $H_{\tau_1}$, and the set $T$ of edges of $H_{\tau_1}$ meeting $B$. Conditional on any exposure $(m,B,T)$ of positive probability, $H_{\tau_1}-B$ is uniform among the simple 3-graphs $G$ on $[n]\setminus B$ with $m_*=m-|T|$ edges satisfying $d_G(w)\ge\ell_w=\max\{0,d_0+1-d_T(w)\}$ for every $w\in[n]\setminus B$:
--   $$P\big[H_{\tau_1}-B=G_0\ \big|\ (\tau_1,B,T)=(m,B_0,T_0)\big]=\begin{cases}1/|\Omega([n]\setminus B_0,m-|T_0|,\ell)|,&G_0\in\Omega([n]\setminus B_0,m-|T_0|,\ell),\\0,&\text{otherwise.}\end{cases}$$
--
--   Differences from the source:
--   - reading: the claim inside "Let n be even and sufficiently large" (proof of Theorem 1.1, p. 14) → ∃ N, the claim for even n ≥ N; reason: standing context of the claim; it needs d₀ ≥ 1 so that all degree-1 vertices lie in B
--   - encoding: H_{τ1} − B is uniform among … → the conditional probability of each G₀ is 1/|Ω'| on Ω' and 0 off it; reason: the definition of the uniform law
--   - encoding: P-admissible exposure → positive probability under the uniform ordering; reason: the paper's definition of P-admissible
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 15, Claim 4.4

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Claim 4.4: for even, sufficiently large `n`, conditional on any exposure `(τ₁, B, T) =
(m, B₀, T₀)` of positive probability, `H_{τ₁} − B` is uniform on the 3-graphs on `[n] \ B₀` with
`m − |T₀|` edges and `d_G(w) ≥ ℓ_w` for every `w ∈ [n] \ B₀`. -/
theorem claim_4_4 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∀ (m : ℕ) (B₀ : Finset (Fin n)) (T₀ : Finset (Finset (Fin n))),
        0 < probOrd n (fun σ => tau1 σ = (m : WithTop ℕ) ∧ lowSet σ = B₀ ∧ exposedEdges σ = T₀) →
        ∀ G₀ : Finset (Finset (Fin n)),
          condProbOrd n (fun σ => deleteVerts (hitGraph σ) (lowSet σ) = G₀)
              (fun σ => tau1 σ = (m : WithTop ℕ) ∧ lowSet σ = B₀ ∧ exposedEdges σ = T₀) =
            if G₀ ∈ OmegaV (Finset.univ \ B₀) (m - T₀.card) (residualBound n T₀) then
              1 / ((OmegaV (Finset.univ \ B₀) (m - T₀.card) (residualBound n T₀)).card : ℝ)
            else 0 := by sorry

end LooseHamHitting.Main
