-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_moment_observables
-- name    : OptimalSpectrum.Entangled.moment_observables
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:21.827337+00:00
-- url     : https://prove2.me/theorems/792fe7ff-edb3-4b56-a2cf-9ac3a212826f
-- title:
--   §7.1.2, Eqs. (38)–(39) — the moment observables are Hermitian, permutation-invariant, commuting, and have mean $\mathrm{tr}((\overline\Pi\tau\overline\Pi)^m)$
-- statement:
--   Let $\overline\Pi$ be an orthogonal projector on $\mathbb C^d$ and let $M_0=dI,M_1,\dots,M_n$ be the moment observables on $(\mathbb C^d)^{\otimes n}$. Then for all $m,m'\le n$:
--
--   1. $M_m$ is Hermitian;
--   2. $M_m$ commutes with every permutation $R_\pi$ of the copies;
--   3. $M_m$ and $M_{m'}$ commute, so all of them can be measured simultaneously;
--   4. for every density matrix $\tau$ on $\mathbb C^d$,
--   $$\mathrm{tr}\big(M_m\tau^{\otimes n}\big)=\mathrm{tr}\big((\overline\Pi\tau\overline\Pi)^m\big);\tag{38}$$
--   5. for every density matrix $\tau$ and every real polynomial $p$ of degree at most $n$,
--   $$\mathrm{tr}\big(\tau^{\otimes n}F_p\big)=\mathrm{tr}\,p\big(\overline\Pi\tau\overline\Pi\big).\tag{39}$$
--
--   With $\tau=\rho$, Eq. (39) says that the entangled estimate $\widehat F_p$ is unbiased for $\mathrm{tr}\,p(\sigma)$.
--
--   Differences from the source:
--   - reading: "all M_m can be simultaneously measured via weak Schur sampling" → the M_m pairwise commute; reason: commuting is the mathematical content of joint measurability of observables
--   - generalization: Eq. (38) for 1 ⩽ m ⩽ K with K ⩽ n, Eq. (39) for deg p ⩽ K → Eq. (38) for all m ⩽ n including m = 0, Eq. (39) for deg p ⩽ n; reason: K ⩽ n is arbitrary (§7.1), and m = 0 holds since M_0 = dI and tr(I) = d; the page's range is a special case
--   - encoding: Π̄ the small-bucket projector of the bucketing output → any orthogonal projector Pbar on ℂ^d; reason: the bucketing output can be any orthogonal projector; the statement is about the observables built from it
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.2, Eqs. (38)–(39), p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_OptimalSpectrum_Entangled_permOp
import Definitions.Def_OptimalSpectrum_Entangled_momentObs
import Definitions.Def_OptimalSpectrum_Entangled_Fobs

open scoped Matrix

namespace OptimalSpectrum.Entangled

/-- **§7.1.2, Eqs. (38)–(39): the moment observables.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.2, printed p. 21 (PDF p. 23): "Each M_m is Hermitian, since every cycle occurs together
with its inverse and commutes with the product of projectors on its support. Each M_m is also
invariant under permutations of the copies. Algorithmically, all M_m can be simultaneously measured
via weak Schur sampling on the retained copies … For every density matrix τ ∈ D(C^d), the trace
identity for cycle permutations gives tr(M_m τ^⊗n) = tr((Π̄τΠ̄)^m), 1 ⩽ m ⩽ K. (38)" and "By Eq. (38),
linearity, and M₀ = dI, tr(τ^⊗n F_p) = tr(p(Π̄τΠ̄)). (39)"

For an orthogonal projector `Π̄` on `ℂ^d` and `m, m' ≤ n`:
1. `M_m` is Hermitian;
2. `M_m` commutes with every copy permutation `R_π`;
3. `M_m` and `M_(m')` commute;
4. `tr(M_m τ^{⊗n}) = tr((Π̄τΠ̄)^m)` for every density matrix `τ` (Eq. (38));
5. `tr(τ^{⊗n} F_p) = tr p(Π̄τΠ̄)` for every density matrix `τ` and real polynomial `p` of degree at
   most `n` (Eq. (39)).

**Formalization Note.** Clause 3 is the mathematical content of "can be simultaneously measured".
The page's range `1 ≤ m ≤ K` with `K ≤ n` (§7.1) is stated for all `m ≤ n`, including `m = 0`
(`M₀ = dI`). -/
theorem moment_observables (d n : ℕ) (Pbar : Matrix (Fin d) (Fin d) ℂ) (hP : Pbar.IsHermitian)
    (hP2 : Pbar * Pbar = Pbar) :
    (∀ m, m ≤ n → (momentObs d n Pbar m).IsHermitian) ∧
    (∀ m, m ≤ n → ∀ π : Equiv.Perm (Fin n),
      permOp π * momentObs d n Pbar m = momentObs d n Pbar m * permOp π) ∧
    (∀ m m', m ≤ n → m' ≤ n → Commute (momentObs d n Pbar m) (momentObs d n Pbar m')) ∧
    (∀ τ : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix τ → ∀ m, m ≤ n →
      Matrix.trace (momentObs d n Pbar m * QAlgorithms.piKron n τ) =
        Matrix.trace ((Pbar * τ * Pbar) ^ m)) ∧
    (∀ τ : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix τ → ∀ p : Polynomial ℝ,
      p.natDegree ≤ n →
      Matrix.trace (QAlgorithms.piKron n τ * Fobs d n Pbar p) =
        Matrix.trace (Polynomial.aeval (Pbar * τ * Pbar) p)) := by sorry

end OptimalSpectrum.Entangled
