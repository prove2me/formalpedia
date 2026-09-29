-- Prove2me | Theorems.Thm_MTT_interpolation_positive_conductor_of_moments
-- name    : MTT.interpolation_positive_conductor_of_moments
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T04:02:27.681397+00:00
-- url     : https://prove2.me/theorems/9dc7d1e5-a932-4445-b169-d9456e6aef88
-- title:
--   MTT interpolation at positive conductor from disk moments
-- statement:
--   Let $p$ be prime, let $N>0$ and $k\ge 2$, and let $f$ be a normalized algebraic cuspidal Hecke eigenform of level $N$ and weight $k$. Fix compatible complex and $p$-adic embeddings, a period system $P$, an ordinary root $\alpha$, and two signed bounded measures $\mu^+$ and $\mu^-$ on $\mathbf Z_p^\times$. Assume each signed measure realizes the prescribed critical polynomial moment on every positive-depth residue disk.
--
--   For every positive integer $n$, every primitive algebraic Dirichlet character $\chi$ modulo $p^n$, and every $0\le j\le k-2$, there are a continuous function $g$ and an algebraic number $v$ such that
--
--   $$
--   g(x)=\iota_p(\chi(x))x^j,\qquad \iota(v)=\frac{p^{n(j+1)}j!\,L(f_{\chi^{-1}},j+1)}{(-2\pi i)^jG(\chi^{-1})\Omega_{\chi(-1)(-1)^j}},
--   $$
--
--   and
--
--   $$
--   (\mu^++\mu^-)(g)=E_p(f,\chi,j,\alpha)\,\iota_p(v),
--   $$
--
--   where $E_p$ is the MTT Euler multiplier. This isolates the positive-conductor part of the interpolation argument, obtained by summing the disk-moment identities against $\chi$ and selecting the sign prescribed by parity.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §14 Proposition, pp. 20–21, positive-conductor case, using (8.6) and (10.2).

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.interpolation_positive_conductor_of_moments
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (μ : Bool → UnitMeasure p)
    (hμ : ∀ s, RealizesMoments f ιp P α s (μ s))
    (n : ℕ) (hn : 0 < n) (χ : DirichletCharacter Qbar (p ^ n))
    (hχ : χ.IsPrimitive) (j : ℕ) (hj : j ≤ k - 2) :
    ∃ (g : C((ℤ_[p])ˣ, ℂ_[p])) (v : Qbar),
      (∀ x, g x = specialFunction ιp n χ j x) ∧
      ι v = normalizedCriticalValue f P.omega n χ j ∧
      (μ true + μ false) g = eulerMultiplier f ιp α n χ j * ιp v := by sorry
