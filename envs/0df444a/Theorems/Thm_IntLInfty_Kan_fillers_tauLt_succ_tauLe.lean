-- Prove2me | Theorems.Thm_IntLInfty_Kan_fillers_tauLt_succ_tauLe
-- name    : IntLInfty.Kan.fillers_tauLt_succ_tauLe
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T02:11:25.02455+00:00
-- url     : https://prove2.me/theorems/174bdeab-6202-41bb-9c6e-3c4e34e154ba
-- title:
--   Horn fillers for $\int\tau_{<n+1}L\to\int\tau_{\le n}L$
-- statement:
--   For every $n,m$ and $0\le j\le m+1$ there is a smooth family of relative horn fillers $$\sigma:\ (\int\tau_{<n+1})_{m+1}\times\mathrm{Hom}(\Lambda[m+1,j]\to\Delta[m+1],\ \int\tau_{<n+1}\to\int\tau_{\le n})\to(\int\tau_{<n+1})_{m+1}.$$
--
--   Role: the filler half of the claim that $\int\tau_{<n+1}L\to\int\tau_{\le n}L$ is a Kan fibration (K2).
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, proof of Theorem 5.10 (Section 5, pp. 15-17)

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

open scoped ContDiff

namespace IntLInfty.Kan

theorem fillers_tauLt_succ_tauLe (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (n : ℕ)
    (h : ∀ i, tauLe δ n i ≤ tauLt δ (n + 1) i) (m : ℕ) (j : Fin (m + 2)) :
    ∃ σ : Amb r (tauLt δ (n + 1)) (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r (tauLt δ (n + 1)) m) × Amb r (tauLe δ n) (m + 1)) →
        Amb r (tauLt δ (n + 1)) (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ (tauLt δ (n + 1)) (m + 1), ∀ y ∈ RelHorn r δ h m j,
          σ x y ∈ integ r δ (tauLt δ (n + 1)) (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
      (∀ x ∈ integ r δ (tauLt δ (n + 1)) (m + 1), σ x (kanMap h m j x) = x) := by sorry

end IntLInfty.Kan
