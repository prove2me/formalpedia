-- Prove2me | Theorems.Thm_LinearDynamics_guarded_periodic_linear_readout
-- name    : LinearDynamics.guarded_periodic_linear_readout
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T19:24:39.578799+00:00
-- url     : https://prove2.me/theorems/67f9341a-d91a-4327-bc34-cdd46dd0a1e8
-- title:
--   Random access to a periodically guarded linear run
-- statement:
--   Let the state space have finite dimension $d$ over a field. A proposed period has length $p>0$. At phase $r$ it prescribes a linear update $A_r$ and a linear observation $g_r$. The actual transition agrees with $A_r$ whenever $g_r$ is zero on the current state. Define the candidate state at time $t=pq+r$ by applying the full-period product $q$ times to the initial state and then applying the first $r$ updates. If the candidate observations are zero at the first $min(T,pd)$ times, then the candidate state equals the actual state at every time at most $T$.
-- source:
--   Combination of the period-product construction and the Cayley–Hamilton observability argument. See Bittanti, Colaneri, and Guardabassi, H-Controllability and Observability of Linear Periodic Systems, https://doi.org/10.1137/0322056, and Kalman, Mathematical Description of Linear Dynamical Systems, https://doi.org/10.1137/0301010.

import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Logic.Function.Iterate

theorem LinearDynamics.guarded_periodic_linear_readout {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (phase : ℕ → Module.End K V) (probe : ℕ → V →ₗ[K] K)
    (p : ℕ) (positive : 0 < p) (step : V → V) (start : V) (T : ℕ)
    (onBranch : ∀ r < p, ∀ x : V, probe r x = 0 → step x = phase r x) :
    let product : ℕ → Module.End K V :=
      Nat.rec 1 (fun r acc => phase r * acc)
    let readout := fun t : ℕ => (product (t % p) * (product p) ^ (t / p)) start
    (∀ t < min T (p * Module.finrank K V), probe (t % p) (readout t) = 0) →
    ∀ t ≤ T, readout t = step^[t] start := by sorry
