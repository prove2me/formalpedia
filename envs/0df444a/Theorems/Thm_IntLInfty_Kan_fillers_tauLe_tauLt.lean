-- Prove2me | Theorems.Thm_IntLInfty_Kan_fillers_tauLe_tauLt
-- name    : IntLInfty.Kan.fillers_tauLe_tauLt
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T02:11:25.847772+00:00
-- url     : https://prove2.me/theorems/8c6505b5-eccc-4962-b5eb-f23e3eaaf024
-- title:
--   Horn fillers for $\int\tau_{\le n}L\to\int\tau_{<n}L$
-- statement:
--   For every $n,m$ and $0\le j\le m+1$ there is a smooth family of relative horn fillers $$\sigma:\ (\int\tau_{\le n})_{m+1}\times\mathrm{Hom}(\Lambda[m+1,j]\to\Delta[m+1],\ \int\tau_{\le n}\to\int\tau_{<n})\to(\int\tau_{\le n})_{m+1}.$$
--
--   Role: the filler half of the claim that $\int\tau_{\le n}L\to\int\tau_{<n}L$ is a Kan fibration (K1).
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

theorem fillers_tauLe_tauLt (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (n : ℕ)
    (h : ∀ i, tauLt δ n i ≤ tauLe δ n i) (m : ℕ) (j : Fin (m + 2)) :
    ∃ σ : Amb r (tauLe δ n) (m + 1) → (({i : Fin (m + 2) // i ≠ j} → Amb r (tauLe δ n) m) × Amb r (tauLt δ n) (m + 1)) →
        Amb r (tauLe δ n) (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ (tauLe δ n) (m + 1), ∀ y ∈ RelHorn r δ h m j,
          σ x y ∈ integ r δ (tauLe δ n) (m + 1) ∧ kanMap h m j (σ x y) = y) ∧
      (∀ x ∈ integ r δ (tauLe δ n) (m + 1), σ x (kanMap h m j x) = x) := by sorry

end IntLInfty.Kan
