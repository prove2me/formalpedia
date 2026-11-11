-- Prove2me | Theorems.Thm_OptLocalHamSim_eq_33
-- name    : OptLocalHamSim.eq_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:47.873307+00:00
-- url     : https://prove2.me/theorems/b504460e-9c4d-4856-a6fb-a6f9ca4ec442
-- title:
--   Eq. (33) — $\int_{0<s_1<\cdots<s_k<h}\prod_i s_i^{q_i}\,ds=h^{\sum_i(q_i+1)}/\prod_ib_i$
-- statement:
--   For $h>0$, $k\ge0$ and exponents $q_1,\dots,q_k\ge0$,
--
--   $$
--   \int_{0<s_1<\cdots<s_k<h}\prod_{i=1}^ks_i^{q_i}\,ds_1\cdots ds_k=\frac{h^{\sum_i(q_i+1)}}{\prod_{i=1}^kb_i},\qquad b_i:=\sum_{a=1}^i(q_a+1).
--   $$
--
--   This evaluates the ordered time integrals of the Dyson expansion in closed form, giving the coefficients of (34).
--
--   Differences from the source:
--   - encoding: the iterated integral over 0 < s₁ < ⋯ < s_k < h → the Lebesgue integral over ℝ^k of the integrand times the indicator of the open chain; reason: the same integral
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), eq. (33), p.17

import Mathlib

namespace OptLocalHamSim

/-- **Eq. (33)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.17: the scalar time integral of the Dyson expansion,
∫_{0<s₁<⋯<s_k<h} ∏_{i=1}^k s_i^{q_i} ds₁⋯ds_k = h^{∑_i(q_i+1)} / ∏_{i=1}^k b_i,
b_i := ∑_{a=1}^i (q_a + 1).

**Formalization Note** The integral is the Lebesgue integral over `Fin k → ℝ` of the integrand times
the indicator of the open chain `0 < s₀ < ⋯ < s_{k−1} < h` (indices from `0`). For `k = 0` both
sides are `1`. -/
theorem eq_33 (k : ℕ) (qq : Fin k → ℕ) (h : ℝ) (hh : 0 < h) :
    ∫ s : Fin k → ℝ, Set.indicator {s : Fin k → ℝ | (∀ i, 0 < s i ∧ s i < h) ∧ StrictMono s}
        (fun s => ∏ i, s i ^ qq i) s =
      h ^ (∑ i, (qq i + 1)) /
        ∏ i, (∑ a ∈ Finset.univ.filter (fun a : Fin k => a ≤ i), ((qq a : ℝ) + 1)) := by sorry

end OptLocalHamSim
