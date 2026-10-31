-- Prove2me | Theorems.Thm_NonlinearPriority_eq_A10
-- name    : NonlinearPriority.eq_A10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:29.499744+00:00
-- url     : https://prove2.me/theorems/7c54b45e-dcd0-4cc2-9e64-a90114948939
-- title:
--   (A.10), p.19 — $M^{\pi_j}_i-M^{\pi_i}_i$ in closed form, and it is positive
-- statement:
--   Assume finite third moments of service, let $i\in\{k,k+1\}$, $j$ the other type, and $\sigma_{k-1}=\sum_{\ell\le k-1}p_\ell\tau^{(2)}_\ell$. Then
--   $$M^{\pi_j}_i-M^{\pi_i}_i=\frac{2\tau^{(3)}}{3\tau^{(2)}(\bar\rho_{k-1}-\rho_j)}+\frac{\lambda\rho_j(\sigma_{k-1}+p_i\tau^{(2)}_i)}{\bar\rho_{k-1}\bar\rho_{k+1}}\Bigl(\frac{1}{\bar\rho_{k-1}-\rho_i}+\frac{1}{\bar\rho_{k-1}-\rho_j}\Bigr)+\frac{\lambda p_j\tau^{(2)}_j}{(\bar\rho_{k-1}-\rho_j)\bar\rho_{k+1}}+\frac{\lambda(\sigma_{k-1}+p_j\tau^{(2)}_j)}{\bar\rho_{k-1}-\rho_j}\Bigl(\frac{1}{\bar\rho_{k-1}}+\frac{1}{\bar\rho_{k-1}-\rho_j}\Bigr),\tag{A.10}$$
--   and this quantity is strictly positive.
--
--   Hence $M^{\pi_i}_i<M^{\pi_j}_i$: a type gains less from priority than it loses from being deprioritized, which gives the strict inequality in Proposition 3 when $c^{(2)}_i>0$.
--
--   Differences from the source:
--   - reading: W^γ_i, 'the steady-state waiting time of a type i customer under policy γ' (p. 4), not defined further → a probability measure w with IsSteadyStateLaw: from every initial state, the waiting times of the successive type-i arrivals converge in distribution to w; E[g(W)] = ∫ g dw; reason: this is how the proof of Lemma A.1(b) (p. 16) uses W^γ_i
--   - encoding: types 1, …, K, pair (k, k+1) with k ∈ {1, …, K−1}; ρ̄_{k−1}, ρ̄_{k+1}, Σ_{ℓ=1}^{k−1}, Σ_{ℓ=1}^{k+1} → Fin K (0-based), pair of types k, k+1 with k+1 < K; rhoBar k, rhoBar (k+2), sumP2 k, sumP2 (k+2); reason: index shift only: the paper's k is k+1 here, and rhoBar m is the paper's ρ̄_m
--   - encoding: 'all moments of service times are positive', finiteness not stated; (A.8)–(A.10) contain τ(3) → finite third moments ∫ x³ dS_i < ∞ for every type; reason: the closed forms are undefined when τ(3) = ∞; this only excludes such instances
--   - encoding: E[W^{π̄k}] and E[(W^{π̄k})²] without a type subscript ('W^{π̄k}_k and W^{π̄k}_{k+1} are identical', p. 5) → the type-i law under π̄_k for each type i of the pair; reason: the literal δ^{γ,π̄k}_i of (3); the paper identifies the two laws
--   - reading: 'without loss of generality, type i customers have priority order i under policy π' (p. 4) → π_k gives type i order i; π_{k+1} swaps the orders of k and k+1; π̄_k gives k and k+1 one common order and keeps the order of all other types; reason: the setting of every displayed formula of the paper (ρ̄_{k−1}, ρ̄_{k+1}, (A.8)–(A.10))
--   - encoding: Poisson arrivals, i.i.d. types and service times; a nonidling, nonpreemptive single server serving the lowest priority order first and FCFS within an order → i.i.d. marks (exponential interarrival, type, one potential service time per type) with product law; the sample path is a recursion over service starts; ties within an order by customer number; a never-started customer gets waiting time 0; reason: customer number is arrival order whenever interarrival times are nonnegative (almost surely), and every customer is started almost surely when ρ < 1, so no instance changes
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, (A.10), proof of Proposition 3, p.19 (PDF 20)

import Mathlib
import Definitions.Def_NonlinearPriority_IsSteadyStateLaw
import Definitions.Def_NonlinearPriority_Mval

open MeasureTheory

namespace NonlinearPriority

/-- **(A.10): `M^{πj}_i − M^{πi}_i` and its positivity** (proof of Proposition 3, p. 19, PDF 20).
Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952:

M^{πj}_i − M^{πi}_i = 2τ(3)/(3τ(2)(ρ̄k−1 − ρj)) + (λρj(Σ_{ℓ=1}^{k−1} pℓτ(2)_ℓ + piτ(2)_i)/(ρ̄k−1 ρ̄k+1))
× (1/(ρ̄k−1 − ρi) + 1/(ρ̄k−1 − ρj)) + λpjτ(2)_j/((ρ̄k−1 − ρj)ρ̄k+1)
+ (λ(Σ_{ℓ=1}^{k−1} pℓτ(2)_ℓ + pjτ(2)_j)/(ρ̄k−1 − ρj))(1/ρ̄k−1 + 1/(ρ̄k−1 − ρj)), (A.10)
"which is positive because 0 < ρj < ρ̄k−1, 0 < ρi < ρ̄k−1, ρ̄k+1 > 0, and all moments of service
times are positive."

For `i` in the pair and `j` the other type, with finite third moments of service.

**Formalization Note.** Index conventions as in `eq_A8_A9`. -/
theorem eq_A10 {K : ℕ} (P : Params K) {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (X : Inputs P Ω Pr)
    (hS3 : ∀ l, Integrable (fun x => x ^ 3) (P.S l))
    (k : ℕ) (i j : Fin K) (hij : ((i : ℕ) = k ∧ (j : ℕ) = k + 1) ∨ ((i : ℕ) = k + 1 ∧ (j : ℕ) = k))
    (w : (Fin K → ℕ) → Fin K → ProbabilityMeasure ℝ)
    (hw : ∀ γ ∈ ({prioPolicy k i, prioPolicy k j, piBar k} : Set (Fin K → ℕ)),
      IsSteadyStateLaw X γ i (w γ i)) :
    Mval w k (prioPolicy k j) i - Mval w k (prioPolicy k i) i =
      2 * P.tauAll 3 / (3 * P.tauAll 2 * (P.rhoBar k - P.rho j)) +
        P.lam * P.rho j * (P.sumP2 k + P.p i * P.tau 2 i) / (P.rhoBar k * P.rhoBar (k + 2)) *
          (1 / (P.rhoBar k - P.rho i) + 1 / (P.rhoBar k - P.rho j)) +
        P.lam * P.p j * P.tau 2 j / ((P.rhoBar k - P.rho j) * P.rhoBar (k + 2)) +
        P.lam * (P.sumP2 k + P.p j * P.tau 2 j) / (P.rhoBar k - P.rho j) *
          (1 / P.rhoBar k + 1 / (P.rhoBar k - P.rho j)) ∧
    0 < Mval w k (prioPolicy k j) i - Mval w k (prioPolicy k i) i := by sorry

end NonlinearPriority
