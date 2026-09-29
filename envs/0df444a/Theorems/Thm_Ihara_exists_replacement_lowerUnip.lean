-- Prove2me | Theorems.Thm_Ihara_exists_replacement_lowerUnip
-- name    : Ihara.exists_replacement_lowerUnip
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/55eee589-b19d-5c38-83d0-01640db346a8
-- title:
--   Mennicke replacement of the upper-left entry modulo A^m
-- statement:
--   Let $q$ be a nonzero natural number, write $\mathbb{Z}[1/q]$ for the localisation `ZAway q` of $\mathbb{Z}$ away from $q$, and let $m$ be a natural number coprime to $q$. Let $\Gamma(m) =$ `principalCongruenceAway m q hmq` denote the kernel of the reduction homomorphism $SL_2(\mathbb{Z}[1/q]) \to SL_2(\mathbb{Z}/m)$ induced by the ring map `zAwayToZMod m q hmq`, and let $Q$ be the normal closure in $SL_2(\mathbb{Z}[1/q])$ of the singleton $\{(\,\mathrm{slToAway}\ q\ \mathrm{mennickeA}\,)^m\}$, i.e. of the $m$-th power of the image of $\begin{pmatrix} 1 & 0 \\ 1 & 1\end{pmatrix}$ under the map $SL_2(\mathbb{Z}) \to SL_2(\mathbb{Z}[1/q])$ induced by $\mathbb{Z} \to \mathbb{Z}[1/q]$. Let $X \in \Gamma(m)$, let $A, B$ be integers and $u, u', v' \in \mathbb{Z}[1/q]$ with $u'v' = 1$ (so $u'$ is a unit with inverse $v'$), and suppose the first row of $X$ has the form $X_{00} = A\,u$ and $X_{01} = B\,u'$, the integers being taken in $\mathbb{Z}[1/q]$ via the structure map. Then for every integer $k$ there exists $X' \in SL_2(\mathbb{Z}[1/q])$ such that $X' \in \Gamma(m)$, the images of $X'$ and $X$ in the quotient $SL_2(\mathbb{Z}[1/q])/Q$ agree, $X'_{00} = (A + Bmk)\,u$, and $X'_{01} = X_{01}$.
--
--   This is the replacement step in Mennicke's analysis of Ihara's modular group: modulo the normal closure of the $m$-th power of the lower unipotent generator, the integer factor of the upper-left entry of a matrix in the principal congruence subgroup of level $m$ may be shifted along the arithmetic progression $A + Bm\mathbb{Z}$, leaving the unit factor $u$ and the whole upper-right entry unchanged. It is used in the proof of [`Ihara.mennickeLemma21`](thm.html#Ihara.mennickeLemma21).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_exists_replacement_lowerUnip.lean

import Definitions.Def_IharaMennickeCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem Ihara.exists_replacement_lowerUnip (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) (X : SL(2, ZAway q))
    (hX : X ∈ principalCongruenceAway m q hmq)
    (A B : ℤ) (u u' v' : ZAway q) (hu'v' : u' * v' = 1)
    (hα : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 = algebraMap ℤ (ZAway q) A * u)
    (hβ : (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 = algebraMap ℤ (ZAway q) B * u') (k : ℤ) :
    ∃ X' : SL(2, ZAway q), X' ∈ principalCongruenceAway m q hmq ∧
      QuotientGroup.mk' (Subgroup.normalClosure
        ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X' =
        QuotientGroup.mk' (Subgroup.normalClosure
          ({(slToAway q mennickeA) ^ m} : Set SL(2, ZAway q))) X ∧
      (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 0 =
        algebraMap ℤ (ZAway q) (A + B * (m : ℤ) * k) * u ∧
      (X' : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 =
        (X : Matrix (Fin 2) (Fin 2) (ZAway q)) 0 1 := by sorry
