-- Prove2me | Theorems.Thm_MTT_interpolation_conductor_one_of_moments
-- name    : MTT.interpolation_conductor_one_of_moments
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T04:02:27.724563+00:00
-- url     : https://prove2.me/theorems/bd33ea0f-cbd0-4554-8367-cf548711f540
-- title:
--   MTT interpolation at conductor one from depth-one moments
-- statement:
--   Let $p$ be prime, let $N>0$ and $k\ge 2$, and let $f$ be a normalized algebraic cuspidal Hecke eigenform of level $N$ and weight $k$. Fix compatible complex and $p$-adic embeddings, a period system $P$, an ordinary root $\alpha$, and two signed bounded measures $\mu^+$ and $\mu^-$ on $\mathbf Z_p^\times$. Assume each signed measure realizes the prescribed critical polynomial moment on every positive-depth residue disk.
--
--   For the primitive character of modulus $p^0=1$ and every $0\le j\le k-2$, there are a continuous function $g$ and an algebraic number $v$ satisfying the conductor-one interpolation identity
--
--   $$
--   (\mu^++\mu^-)(g)=E_p(f,\chi,j,\alpha)\,\iota_p(v),
--   $$
--
--   with $g(x)=\iota_p(\chi(x))x^j$ and $\iota(v)$ equal to the corresponding period-normalized critical value. Both Euler factors in $E_p$ are retained. This is the boundary case recovered by partitioning $\mathbf Z_p^\times$ into residue disks of depth one and applying the moment relations there.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), https://doi.org/10.1007/BF01388731; Chapter I, §14 Proposition, pp. 20–21, conductor-one case, using (8.6) and (10.2).

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.interpolation_conductor_one_of_moments
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (μ : Bool → UnitMeasure p)
    (hμ : ∀ s, RealizesMoments f ιp P α s (μ s))
    (χ : DirichletCharacter Qbar (p ^ 0)) (hχ : χ.IsPrimitive)
    (j : ℕ) (hj : j ≤ k - 2) :
    ∃ (g : C((ℤ_[p])ˣ, ℂ_[p])) (v : Qbar),
      (∀ x, g x = specialFunction ιp 0 χ j x) ∧
      ι v = normalizedCriticalValue f P.omega 0 χ j ∧
      (μ true + μ false) g = eulerMultiplier f ιp α 0 χ j * ιp v := by sorry
