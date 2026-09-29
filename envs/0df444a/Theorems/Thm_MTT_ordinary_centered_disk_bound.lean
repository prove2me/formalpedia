-- Prove2me | Theorems.Thm_MTT_ordinary_centered_disk_bound
-- name    : MTT.ordinary_centered_disk_bound
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T01:34:19.995221+00:00
-- url     : https://prove2.me/theorems/d678f59b-8280-4868-b9ab-84d81752bb5b
-- title:
--   Ordinary centred disk-moment bound in every critical degree
-- statement:
--   Fix a prime $p$, a positive level $N$, and a weight $k\ge2$. Let $f$ be a normalized algebraic cuspidal Hecke eigenform, with fixed embeddings into $\mathbf C$ and $\mathbf C_p$, a signed period system $P$ with finitely generated integral lattice, and an ordinary root $\alpha$ of its Hecke polynomial.
--
--   Write $M_{s,t}(n,a)$ for the signed degree-$t$ disk moment defined by MTT (10.2), and define its centred degree-$j$ moment by
--   $$M^{\mathrm{cent}}_{s,j}(n,a)=\sum_{t=0}^j\binom jt(-a)^{j-t}M_{s,t}(n,a).$$
--   There exists a real constant $C\ge0$, independent of the sign $s$, depth $n\ge1$, integer centre $a$, and degree $0\le j\le k-2$, such that
--   $$\left|M^{\mathrm{cent}}_{s,j}(n,a)\right|_p\le C p^{-nj}.$$
--
--   This is the slope-zero centred-moment estimate in MTT I.§11. Its degree-zero case bounds disk masses, while the positive-degree decay controls polynomial approximation on shrinking disks. It is the bound needed to recover all critical polynomial moments when extending the distribution to a bounded measure.
--
--   **Formalization Note** The left side is expressed directly as a binomial sum of the existing disk moments, without assuming a measure already exists. The right side uses the norm of $p^{nj}$ in $\mathbf C_p$.
-- source:
--   Mazur–Tate–Teitelbaum, On p-adic analogues of the conjectures of Birch and Swinnerton-Dyer, Invent. Math. 84 (1986), Chapter I, §11, property III and the centred estimate III_h on p. 15, specialized to an ordinary root (slope zero), with disk moments from (10.2). https://doi.org/10.1007/BF01388731

import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.ordinary_centered_disk_bound
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Bool) (n : ℕ), 0 < n →
      ∀ (a : ℤ) (j : ℕ), j ≤ k - 2 →
        ‖∑ t ∈ Finset.range (j + 1),
          (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
            diskMoment f ιp P α s t n a‖ ≤
          C * ‖(p : ℂ_[p]) ^ (n * j)‖ := by sorry
